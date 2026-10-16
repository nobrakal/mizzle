From stdpp Require Import relations.
From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi.lib Require Import fixpoint_mono.

From mizzle.lang Require Import instances.

From mizzle.logic Require Import interp goal adequacy translate decompose wf_access.

Section utils.

Context `{seqlogGS Σ}.

Lemma big_sepL_heap_array (Φ : location → val → iProp Σ) l vs :
  ([∗ list] i ↦ v ∈ vs, Φ (l +ₗ i) v) ⊢
  [∗ map] l' ↦ v ∈ chunk l vs, Φ l' v.
Proof.
  revert l. induction vs as [|v vs IH]; intros l; simpl.
  { iIntros "_". done. }
  iIntros "[H Hrest]".
  rewrite big_sepM_insert.
  2:{ apply eq_None_ne_Some. intros v0 (k & Hk & Hl & _)%chunk_lookup.
      rewrite -{1}(location_add_0 l) in Hl. naive_solver lia. }
  rewrite location_add_0. iFrame.
  iApply IH.
  iApply (big_sepL_mono with "Hrest"). intros k v' Hk.
  rewrite location_add_assoc. f_equiv. f_equiv. lia.
Qed.

(* φ : list of physical thread ids (one per logical thread).
   ψ : bijection physical → logical locations.
   The logical tid is the position in φ; φ[i] is the physical id used by interp.
   NoDup φ encodes injectivity for threads. *)

(** [block_aligned ψ σ]: [ψ] respects [σ]'s block structure — same offset on
    both sides — letting [tr_loc_offset] commute [tr_loc] with [+ₗ] in-bounds. *)
Definition block_aligned (ψ : gmap location location) (σ : state) : Prop :=
  ∀ l hdr, σ.(state_headers) !! l = Some hdr →
  ∀ i, (i < header_size hdr)%nat →
  ∃ l', ψ !! l = Some l' ∧
        ψ !! (l +ₗ Z.of_nat i) = Some (l' +ₗ Z.of_nat i).

(** Translated contents of the block at [l] of size [sz]: the [ψ]-translated
    heap values at offsets [0 .. sz-1]. *)
Definition block_vals (ψ : gmap location location) (σ : state)
                      (l : location) (sz : nat) : list val :=
  (λ i, tr_val ψ (default ValUnit (σ.(state_heap) !! (l +ₗ Z.of_nat i)))) <$> seq 0 sz.

(** [heap_partition σ]: [σ]'s heap is exactly the disjoint union of its
    blocks. Three conjuncts:
    - completeness: every header's cells are present;
    - covered: every heap cell lies in some block;
    - disjoint: distinct (block, offset) pairs address distinct cells. *)
Definition heap_partition (σ : state) : Prop :=
  (∀ l hdr, σ.(state_headers) !! l = Some hdr →
            ∀ i, (i < header_size hdr)%nat →
                 is_Some (σ.(state_heap) !! (l +ₗ Z.of_nat i))) ∧
  (∀ k, k ∈ dom σ.(state_heap) →
        ∃ l hdr i, σ.(state_headers) !! l = Some hdr ∧
                   (i < header_size hdr)%nat ∧ k = l +ₗ Z.of_nat i) ∧
  (∀ l1 hdr1 l2 hdr2 i1 i2,
     σ.(state_headers) !! l1 = Some hdr1 → σ.(state_headers) !! l2 = Some hdr2 →
     (i1 < header_size hdr1)%nat → (i2 < header_size hdr2)%nat →
     l1 +ₗ Z.of_nat i1 = l2 +ₗ Z.of_nat i2 → l1 = l2 ∧ i1 = i2).

(** Pure invariants linking the physical state to the bijection [ψ].

    - [ei_nodup]/[ei_len]: well-formedness of the thread/local indexing.
    - [ei_dom_h]/[ei_dom_hd]: [ψ] covers every allocated physical location.
    - [ei_dom_ψ] (Invariant A): [ψ] tracks *exactly* the allocated locations.
    - [ei_img_ψ] (Invariant B): every logical location in [codom ψ] is the
      image under [tr_loc] of a physical location we own a resource for.
    - [ei_inj]: [ψ] is injective.
    - [ei_wfes]/[ei_wfls]/[ei_wfhp] (Invariant C): every physical location
      mentioned by in-flight code, locals, or heap values lives in [dom ψ].
      This makes [tr_expr] / [tr_val] stable under ψ-extensions at fresh keys.
    - [ei_block]: [ψ] respects block structure — for every allocated block
      (witnessed by a header at [l] with size [sz]), [ψ] maps the contiguous
      range [l..l +ₗ (sz-1)] to a contiguous range [l'..l' +ₗ (sz-1)]. This
      justifies [tr_loc_offset] within bounds.
    - [ei_part]: the heap is exactly the disjoint union of its blocks
      ([heap_partition]). *)
Record mirror_invs (φ : list nat) (ψ : gmap location location)
                     (es : list expr) (σ : state) : Prop := {
  ei_nodup  : NoDup φ;
  ei_len    : length es = length σ.(state_locals);
  ei_dom_h  : dom σ.(state_heap) ⊆ dom ψ;
  ei_dom_hd : dom σ.(state_headers) ⊆ dom ψ;
  ei_dom_ψ  : dom ψ ⊆ dom σ.(state_heap) ∪ dom σ.(state_headers);
  ei_img_ψ  : map_img ψ ⊆@{gset _}
                set_map (tr_loc ψ) (dom σ.(state_heap) ∪ dom σ.(state_headers));
  ei_inj    : tr_inj ψ;
  ei_wfes   : Forall (wf_expr ψ) es;
  ei_wfls   : Forall (wf_val ψ) σ.(state_locals);
  ei_wfhp   : map_Forall (λ _ v, wf_val ψ v) σ.(state_heap);
  ei_block  : block_aligned ψ σ;
  ei_part   : heap_partition σ;
}.

(** Set of source locations that are headers without a heap cell at the
    same address (i.e., size-0 source blocks). For every such [l] the
    live-location token [loc_tok1 (tr_loc ψ l)] is held separately by
    [mirror]; non-orphan headers piggyback their token on the
    bundled heap cell at offset 0. *)
Definition orphan_headers (σ : state) : gset location :=
  dom σ.(state_headers) ∖ dom σ.(state_heap).

(** Block-structured heap ownership: each header [l ↦ h] owns the whole
    block — the (persistent) header together with the contiguous cells at
    [tr_loc ψ l +ₗ i]. The header travels with the block, bundling
    [wf_access]'s witness into the points-to. *)
Definition heap_blocks (ψ : gmap location location) (σ : state) : iProp Σ :=
  [∗ map] l ↦ h ∈ σ.(state_headers),
    tr_loc ψ l ↦ₕ□ h ∗
    ([∗ list] i ↦ v ∈ block_vals ψ σ l (header_size h),
       (tr_loc ψ l +ₗ Z.of_nat i) ↦ v).

(** Well-formedness of the real trace under [ψ]: every emitted value's
    locations are already tracked by [ψ]. Maintained because emitted values
    come from in-flight code (which is [wf_expr ψ]) and [ψ] only grows; it is
    what makes the shadow trace stable under [ψ]-extension at fresh keys. *)
Definition trace_wf (ψ : gmap location location) (κ : list observation) : Prop :=
  Forall (wf_val ψ) κ.

(** Combined pure invariant carried by [mirror]: the configuration invariants
    [mirror_invs] together with [trace_wf]. *)
Definition mirror_ok (φ : list nat) (ψ : gmap location location)
                     (es : list expr) (σ : state) (κ : list observation) : Prop :=
  mirror_invs φ ψ es σ ∧ trace_wf ψ κ.

(** [ψ]-extension at fresh keys does not change the renamed trace, provided
    the observations are [trace_wf]. *)
Lemma tr_trace_extend ψ ψ' κ :
  (∀ k, k ∈ dom ψ → ψ' !! k = ψ !! k) →
  trace_wf ψ κ →
  tr_val ψ' <$> κ = tr_val ψ <$> κ.
Proof.
  intros Hagree. rewrite /trace_wf. induction κ as [|o os IH].
  { done. }
  intros [Hwf Htail]%Forall_cons. simpl. f_equal.
  - by rewrite (tr_val_extend ψ ψ' o Hagree Hwf).
  - by apply IH.
Qed.

(** [trace_wf] is monotone in [dom ψ]. *)
Lemma trace_wf_mono ψ ψ' κ :
  dom ψ ⊆ dom ψ' → trace_wf ψ κ → trace_wf ψ' κ.
Proof.
  intros Hsub Hwf. rewrite /trace_wf in Hwf |- *.
  eapply Forall_impl; [exact Hwf|].
  intros o H1. rewrite /wf_val in H1 |- *. set_solver.
Qed.

(** [mirror] additionally owns the shadow trace, pinned to the [ψ]-renaming
    of the real reduction trace [κ]. [Emit]-recorded events accumulate there
    as the shadow run proceeds; the [κ] index reveals the real trace, the hook
    for a linearizability completeness statement. *)
Definition mirror (es:list expr) (σ:state) (κ : list observation) : iProp Σ :=
  ∃ (φ:list nat) (ψ:gmap location location),
    ⌜mirror_ok φ ψ es σ κ⌝ ∗
    ([∗ list] p; e ∈ φ; es,               running p (tr_expr ψ e)) ∗
    ([∗ list] p; v ∈ φ; σ.(state_locals), local   p (tr_val  ψ v)) ∗
    heap_blocks ψ σ ∗
    ([∗ set] l ∈ orphan_headers σ,        loc_tok1 (tr_loc ψ l)) ∗
    trace_model (tr_val ψ <$> κ).

(** Regroup a [chunk] under any predicate as a list indexed by offset. *)
Lemma big_sepM_chunk (Φ : location → val → iProp Σ) l (vs : list val) :
  ([∗ map] k↦v ∈ chunk l vs, Φ k v) ⊣⊢ [∗ list] i↦v ∈ vs, Φ (l +ₗ Z.of_nat i) v.
Proof.
  revert l. induction vs as [|v vs IH]; intros l; simpl.
  { by rewrite big_sepM_empty. }
  rewrite big_sepM_insert; last first.
  { destruct (chunk (l +ₗ 1) vs !! l) eqn:Hl; last done.
    exfalso. apply chunk_lookup in Hl as (j & ? & Hj & _).
    rewrite location_add_assoc in Hj. rewrite -{1}(location_add_0 l) in Hj.
    apply (inj (location_add l)) in Hj. lia. }
  rewrite location_add_0. rewrite (IH (l +ₗ 1)).
  apply bi.sep_proper; first done.
  apply big_sepL_proper => i v' _.
  rewrite Nat2Z.inj_succ -Z.add_1_l location_add_assoc //.
Qed.

(** Peel a single block (the cells at offsets [0..length vs-1], whose values
    are [vs]) out of a flat heap [hp], leaving the rest. *)
Lemma heap_block_peel ψ (hp : gmap location val) l (vs : list val) :
  (∀ i, (i < length vs)%nat → tr_loc ψ (l +ₗ Z.of_nat i) = tr_loc ψ l +ₗ Z.of_nat i) →
  (∀ i v, vs !! i = Some v → hp !! (l +ₗ Z.of_nat i) = Some v) →
  ([∗ map] k↦v ∈ hp, tr_loc ψ k ↦ tr_val ψ v) ⊣⊢
    ([∗ list] i↦v ∈ vs, (tr_loc ψ l +ₗ Z.of_nat i) ↦ tr_val ψ v)
    ∗ ([∗ map] k↦v ∈ hp ∖ chunk l vs, tr_loc ψ k ↦ tr_val ψ v).
Proof.
  intros Halign Hvals.
  assert (Hsub : chunk l vs ⊆ hp).
  { apply map_subseteq_spec. intros k v Hk.
    apply chunk_lookup in Hk as (i & Hi0 & -> & Hvi).
    pose proof (Hvals (Z.to_nat i) v Hvi) as Hh.
    rewrite Z2Nat.id in Hh; [exact Hh | exact Hi0]. }
  rewrite -{1}(map_difference_union (chunk l vs) hp Hsub).
  rewrite big_sepM_union; last by apply map_disjoint_difference_r1.
  rewrite big_sepM_chunk.
  apply bi.sep_proper; last done.
  apply big_sepL_proper => i v Hi.
  rewrite Halign //. by eapply lookup_lt_Some.
Qed.

(** Membership in a [chunk]'s domain, by offset. *)
Lemma elem_of_dom_chunk k l (vs : list val) :
  k ∈ dom (chunk l vs) ↔ ∃ i, (i < length vs)%nat ∧ k = l +ₗ Z.of_nat i.
Proof.
  rewrite elem_of_dom. split.
  - intros [v (i & Hi0 & -> & Hvi)%chunk_lookup].
    exists (Z.to_nat i). rewrite Z2Nat.id //. split; last done.
    by eapply lookup_lt_Some.
  - intros (i & Hi & ->).
    destruct (lookup_lt_is_Some_2 vs i Hi) as [v Hv].
    exists v. apply chunk_lookup. exists (Z.of_nat i). rewrite Nat2Z.id.
    split_and!; [lia|done|done].
Qed.

(** The cells-half of [heap_blocks], over a sub-collection [m] of headers and a
    heap [hp] partitioned by exactly those blocks, equals the flat heap [hp].
    Proved by carving one block off [hp] per header. *)
Lemma cells_flat_gen ψ (m : gmap location header) :
  ∀ (hp : gmap location val),
  (∀ l h, m !! l = Some h → ∀ i, (i < header_size h)%nat →
          is_Some (hp !! (l +ₗ Z.of_nat i))) →
  (∀ k, k ∈ dom hp → ∃ l h i, m !! l = Some h ∧ (i < header_size h)%nat ∧
          k = l +ₗ Z.of_nat i) →
  (∀ l1 h1 l2 h2 i1 i2, m !! l1 = Some h1 → m !! l2 = Some h2 →
     (i1 < header_size h1)%nat → (i2 < header_size h2)%nat →
     l1 +ₗ Z.of_nat i1 = l2 +ₗ Z.of_nat i2 → l1 = l2 ∧ i1 = i2) →
  (∀ l h, m !! l = Some h → ∀ i, (i < header_size h)%nat →
     tr_loc ψ (l +ₗ Z.of_nat i) = tr_loc ψ l +ₗ Z.of_nat i) →
  ([∗ map] l ↦ h ∈ m,
     [∗ list] i ↦ v ∈ ((λ i, default ValUnit (hp !! (l +ₗ Z.of_nat i)))
                          <$> seq 0 (header_size h)),
       (tr_loc ψ l +ₗ Z.of_nat i) ↦ tr_val ψ v)
  ⊣⊢ [∗ map] k ↦ v ∈ hp, tr_loc ψ k ↦ tr_val ψ v.
Proof.
  induction m as [|l h m' Hl IH] using map_ind;
    intros hp Hcompl Hcov Hdisj Halign.
  - assert (hp = ∅) as ->.
    { apply map_empty. intros k. destruct (hp !! k) as [v|] eqn:E; last done.
      exfalso. destruct (Hcov k) as (?&?&?&Hk&_); first by (apply elem_of_dom; eauto).
      by rewrite lookup_empty in Hk. }
    by rewrite !big_sepM_empty.
  - set (svs_l := (λ i, default ValUnit (hp !! (l +ₗ Z.of_nat i)))
                    <$> seq 0 (header_size h)).
    assert (Hml : (<[l := h]> m') !! l = Some h) by apply lookup_insert_eq.
    assert (Hlensvs : length svs_l = header_size h)
      by (rewrite /svs_l length_fmap length_seq //).
    assert (Halign_l : ∀ i, (i < length svs_l)%nat →
              tr_loc ψ (l +ₗ Z.of_nat i) = tr_loc ψ l +ₗ Z.of_nat i).
    { intros i Hi. rewrite Hlensvs in Hi. by apply (Halign l h Hml). }
    assert (Hvals_l : ∀ i v, svs_l !! i = Some v → hp !! (l +ₗ Z.of_nat i) = Some v).
    { intros i v Hi.
      assert (Hi' : (i < header_size h)%nat).
      { apply lookup_lt_Some in Hi. by rewrite Hlensvs in Hi. }
      rewrite /svs_l list_lookup_fmap lookup_seq_lt // /= in Hi.
      destruct (Hcompl l h Hml i Hi') as [v0 Hv0]. rewrite Hv0 in Hi |- *. by simplify_eq. }
    rewrite (heap_block_peel ψ hp l svs_l Halign_l Hvals_l).
    rewrite big_sepM_insert //.
    apply bi.sep_proper; first done.
    (* swap [hp] for [hp ∖ chunk l svs_l] in the remaining blocks, then IH *)
    rewrite -(IH (hp ∖ chunk l svs_l)).
    + apply big_sepM_proper. intros l' h' Hl'.
      assert (Hne : l' ≠ l) by congruence.
      assert (Hml' : (<[l := h]> m') !! l' = Some h')
        by (rewrite lookup_insert_ne; [exact Hl'|congruence]).
      assert (Heqv : ∀ i, (i < header_size h')%nat →
                hp !! (l' +ₗ Z.of_nat i) = (hp ∖ chunk l svs_l) !! (l' +ₗ Z.of_nat i)).
      { intros i Hi. rewrite lookup_difference.
        destruct (chunk l svs_l !! (l' +ₗ Z.of_nat i)) as [x|] eqn:E; last done.
        exfalso. apply mk_is_Some, elem_of_dom, elem_of_dom_chunk in E as (j & Hj & Heq).
        rewrite Hlensvs in Hj.
        destruct (Hdisj l' h' l h i j Hml' Hml Hi Hj Heq) as [Hll _].
        apply Hne, Hll. }
      assert (Hlists : (λ i, default ValUnit (hp !! (l' +ₗ Z.of_nat i))) <$> seq 0 (header_size h')
                = (λ i, default ValUnit ((hp ∖ chunk l svs_l) !! (l' +ₗ Z.of_nat i))) <$> seq 0 (header_size h')).
      { apply list_fmap_ext. intros i j Hj.
        apply lookup_seq in Hj as [-> Hjlt]. by rewrite Heqv. }
      by rewrite Hlists.
    + intros l0 h0 Hl0 i Hi.
      assert (Hne : l0 ≠ l) by congruence.
      assert (Hml0 : (<[l := h]> m') !! l0 = Some h0)
        by (rewrite lookup_insert_ne; [exact Hl0|congruence]).
      rewrite lookup_difference.
      destruct (chunk l svs_l !! (l0 +ₗ Z.of_nat i)) as [x|] eqn:E;
        last by apply (Hcompl l0 h0).
      exfalso. apply mk_is_Some, elem_of_dom, elem_of_dom_chunk in E as (j & Hj & Heq).
      rewrite Hlensvs in Hj.
      destruct (Hdisj l0 h0 l h i j Hml0 Hml Hi Hj Heq) as [Hll _].
      apply Hne, Hll.
    + intros k Hk.
      assert (Hkin : k ∈ dom hp).
      { apply elem_of_dom. apply elem_of_dom in Hk as [v Hv].
        rewrite lookup_difference in Hv.
        destruct (chunk l svs_l !! k); [done|by eauto]. }
      destruct (Hcov k Hkin) as (l0 & h0 & i & Hl0 & Hi & ->).
      assert (Hne : l0 ≠ l).
      { intros ->. apply elem_of_dom in Hk as [v Hv]. rewrite lookup_difference in Hv.
        assert (Hin : l +ₗ Z.of_nat i ∈ dom (chunk l svs_l)).
        { apply elem_of_dom_chunk. exists i. rewrite Hlensvs. split; last done.
          rewrite lookup_insert_eq in Hl0. by simplify_eq. }
        apply elem_of_dom in Hin as [? HH]. by rewrite HH in Hv. }
      exists l0, h0, i. rewrite lookup_insert_ne in Hl0; [|congruence].
      split_and!; [exact Hl0|done|done].
    + intros l1 h1 l2 h2 i1 i2 H1 H2 Hi1 Hi2 Heq.
      assert (l1 ≠ l) by congruence. assert (l2 ≠ l) by congruence.
      apply (Hdisj l1 h1 l2 h2 i1 i2); try done; rewrite lookup_insert_ne //.
    + intros l0 h0 Hl0 i Hi. apply (Halign l0 h0); last done.
      rewrite lookup_insert_ne; [exact Hl0|congruence].
Qed.

(** Bridge: under [block_aligned] + [heap_partition], the block-structured
    heap ownership is the flat per-cell heap together with the per-header
    points-to. This lets the simulation reason on the flat heap (as before)
    while [mirror] stays block-structured. *)
Lemma heap_blocks_flat ψ σ :
  block_aligned ψ σ → heap_partition σ →
  heap_blocks ψ σ ⊣⊢
    ([∗ map] l ↦ v ∈ σ.(state_heap), tr_loc ψ l ↦ tr_val ψ v) ∗
    ([∗ map] l ↦ h ∈ σ.(state_headers), tr_loc ψ l ↦ₕ□ h).
Proof.
  intros Halign (Hcompl & Hcov & Hdisj).
  assert (Halign' : ∀ l h, σ.(state_headers) !! l = Some h → ∀ i, (i < header_size h)%nat →
            tr_loc ψ (l +ₗ Z.of_nat i) = tr_loc ψ l +ₗ Z.of_nat i).
  { intros l h Hl i Hi. destruct (Halign l h Hl i Hi) as (l' & Hψl & Hψli).
    rewrite /tr_loc Hψl Hψli //. }
  rewrite /heap_blocks big_sepM_sep.
  assert (Hcells :
    ([∗ map] l ↦ h ∈ σ.(state_headers),
       [∗ list] i ↦ v ∈ block_vals ψ σ l (header_size h), (tr_loc ψ l +ₗ Z.of_nat i) ↦ v)
    ⊣⊢ [∗ map] k ↦ v ∈ σ.(state_heap), tr_loc ψ k ↦ tr_val ψ v).
  { rewrite -(cells_flat_gen ψ σ.(state_headers) σ.(state_heap) Hcompl Hcov Hdisj Halign').
    apply big_sepM_proper. intros l h Hl. rewrite /block_vals !big_sepL_fmap //. }
  rewrite Hcells. by rewrite bi.sep_comm.
Qed.

Lemma mirror_unfold es σ κ :
  mirror es σ κ ⊣⊢
  ∃ (φ:list nat) (ψ:gmap location location),
    ⌜mirror_ok φ ψ es σ κ⌝ ∗
    ([∗ list] p; e ∈ φ; es,               running p (tr_expr ψ e)) ∗
    ([∗ list] p; v ∈ φ; σ.(state_locals), local   p (tr_val  ψ v)) ∗
    ([∗ map] l ↦ v ∈ σ.(state_heap),      tr_loc ψ l ↦ tr_val ψ v) ∗
    ([∗ map] l ↦ h ∈ σ.(state_headers),   tr_loc ψ l ↦ₕ□ h) ∗
    ([∗ set] l ∈ orphan_headers σ,        loc_tok1 (tr_loc ψ l)) ∗
    trace_model (tr_val ψ <$> κ).
Proof.
  rewrite /mirror.
  iSplit.
  - iIntros "(%φ & %ψ & %Hok & Hrun & Hloc & Hh & Horph & Hpm)".
    pose proof (proj1 Hok) as Hinv.
    rewrite (heap_blocks_flat _ _ (ei_block _ _ _ _ Hinv) (ei_part _ _ _ _ Hinv)).
    iDestruct "Hh" as "[Hheap Hhdrs]". iExists φ, ψ. by iFrame.
  - iIntros "(%φ & %ψ & %Hok & Hrun & Hloc & Hheap & Hhdrs & Horph & Hpm)".
    pose proof (proj1 Hok) as Hinv.
    iExists φ, ψ.
    rewrite (heap_blocks_flat _ _ (ei_block _ _ _ _ Hinv) (ei_part _ _ _ _ Hinv)).
    by iFrame.
Qed.

(** Gather a single block out of the flat heap (for the field-access
    branches), returning the block as a [↦∗] and a wand to restore the
    flat heap after a write. *)
Lemma heap_block_gather ψ σ l tag sz (fld : Z) :
  block_aligned ψ σ → heap_partition σ →
  σ.(state_headers) !! l = Some (Header tag sz) →
  (0 ≤ fld < Z.of_nat sz)%Z →
  tr_loc ψ l ↦ₕ□ Header tag sz -∗
  ([∗ map] k ↦ v ∈ σ.(state_heap), tr_loc ψ k ↦ tr_val ψ v) -∗
  ∃ vs, ⌜length vs = sz ∧
         vs !! Z.to_nat fld
           = Some (tr_val ψ (default ValUnit (σ.(state_heap) !! (l +ₗ fld))))⌝ ∗
        tr_loc ψ l ↦∗ vs ∗
        (∀ w, tr_loc ψ l ↦∗ <[Z.to_nat fld := tr_val ψ w]> vs -∗
              [∗ map] k ↦ v ∈ <[l +ₗ fld := w]> σ.(state_heap),
                tr_loc ψ k ↦ tr_val ψ v).
Proof.
  intros Halignσ Hpart Hhdr Hfld. destruct Hpart as (Hcompl & _ & _).
  assert (Halign : ∀ i, (i < sz)%nat →
            tr_loc ψ (l +ₗ Z.of_nat i) = tr_loc ψ l +ₗ Z.of_nat i).
  { intros i Hi. destruct (Halignσ l (Header tag sz) Hhdr i Hi) as (l' & Hψl & Hψli).
    rewrite /tr_loc Hψl Hψli //. }
  set (svs := (λ i, default ValUnit (σ.(state_heap) !! (l +ₗ Z.of_nat i))) <$> seq 0 sz).
  assert (Hlensvs : length svs = sz) by (rewrite /svs length_fmap length_seq //).
  assert (Hsval : ∀ i, (i < sz)%nat → svs !! i = Some (default ValUnit (σ.(state_heap) !! (l +ₗ Z.of_nat i)))).
  { intros i Hi. rewrite /svs list_lookup_fmap lookup_seq_lt //. }
  assert (Hsvs : ∀ i v, svs !! i = Some v → σ.(state_heap) !! (l +ₗ Z.of_nat i) = Some v).
  { intros i v Hi.
    assert (Hi' : (i < sz)%nat).
    { apply lookup_lt_Some in Hi. by rewrite Hlensvs in Hi. }
    destruct (Hcompl l (Header tag sz) Hhdr i Hi') as [v0 Hv0]. simpl in Hv0.
    rewrite Hsval // Hv0 /= in Hi. rewrite Hv0. by simplify_eq. }
  assert (Halign' : ∀ i, (i < length svs)%nat →
            tr_loc ψ (l +ₗ Z.of_nat i) = tr_loc ψ l +ₗ Z.of_nat i).
  { rewrite Hlensvs. exact Halign. }
  iIntros "#Hh Hheap".
  rewrite (heap_block_peel ψ σ.(state_heap) l svs Halign' Hsvs).
  iDestruct "Hheap" as "[Hcells Hrest]".
  iExists (tr_val ψ <$> svs).
  iSplit.
  { iPureIntro. split.
    - by rewrite length_fmap Hlensvs.
    - rewrite list_lookup_fmap.
      rewrite Hsval; last lia. rewrite /= Z2Nat.id; [done|lia]. }
  iSplitR "Hrest".
  { rewrite /mz_block. iExists tag. rewrite length_fmap Hlensvs. iFrame "Hh".
    rewrite big_sepL_fmap. iFrame "Hcells". }
  iIntros (w) "Hblk".
  set (svs' := <[Z.to_nat fld := w]> svs).
  assert (Hlt : (Z.to_nat fld < sz)%nat) by lia.
  assert (Hlensvs' : length svs' = sz) by (rewrite /svs' length_insert Hlensvs //).
  assert (Halign'' : ∀ i, (i < length svs')%nat →
            tr_loc ψ (l +ₗ Z.of_nat i) = tr_loc ψ l +ₗ Z.of_nat i).
  { rewrite Hlensvs'. exact Halign. }
  assert (Hsvs' : ∀ i v, svs' !! i = Some v →
            (<[l +ₗ fld := w]> σ.(state_heap)) !! (l +ₗ Z.of_nat i) = Some v).
  { intros i v Hi.
    assert (Hi' : (i < sz)%nat).
    { apply lookup_lt_Some in Hi. by rewrite Hlensvs' in Hi. }
    destruct (decide (i = Z.to_nat fld)) as [->|Hne].
    - rewrite /svs' list_lookup_insert_eq in Hi; last by rewrite Hlensvs.
      rewrite Z2Nat.id; last lia. rewrite lookup_insert_eq. by simplify_eq.
    - rewrite /svs' list_lookup_insert_ne // in Hi.
      rewrite lookup_insert_ne; first by apply Hsvs.
      intros Heq. apply (inj (location_add l)) in Heq.
      apply Hne. lia. }
  assert (Hdomeq : dom (chunk l svs') = dom (chunk l svs)).
  { apply set_eq. intros x. rewrite !elem_of_dom_chunk Hlensvs Hlensvs'. done. }
  assert (Hfld_in : (l +ₗ fld) ∈ dom (chunk l svs')).
  { apply elem_of_dom_chunk. exists (Z.to_nat fld). split.
    - rewrite Hlensvs'. lia.
    - rewrite (Z2Nat.id fld); [done|lia]. }
  assert (Hdiff : (<[l +ₗ fld := w]> σ.(state_heap)) ∖ chunk l svs'
                  = σ.(state_heap) ∖ chunk l svs).
  { apply map_eq. intros k0. rewrite !lookup_difference.
    destruct (chunk l svs !! k0) as [x|] eqn:E;
    destruct (chunk l svs' !! k0) as [x'|] eqn:E'; try done.
    - exfalso. apply mk_is_Some, elem_of_dom in E. rewrite -Hdomeq in E.
      apply elem_of_dom in E as [? HE]. by rewrite HE in E'.
    - exfalso. apply mk_is_Some, elem_of_dom in E'. rewrite Hdomeq in E'.
      apply elem_of_dom in E' as [? HE]. by rewrite HE in E.
    - assert (Hne0 : l +ₗ fld ≠ k0).
      { intros Heq. rewrite Heq in Hfld_in.
        apply elem_of_dom in Hfld_in as [? HH]. by rewrite HH in E'. }
      rewrite lookup_insert_ne //. }
  rewrite (heap_block_peel ψ (<[l +ₗ fld := w]> σ.(state_heap)) l svs' Halign'' Hsvs').
  rewrite Hdiff.
  rewrite /mz_block. iDestruct "Hblk" as (tag') "[_ Hcells']".
  iEval (rewrite -list_fmap_insert big_sepL_fmap) in "Hcells'".
  iSplitL "Hcells'"; [iApply "Hcells'" | iApply "Hrest"].
Qed.

(** Closing tactic for cases that don't alter [state_heap] or [state_locals].
    Leaves the [Forall (wf_expr ψ) (<[tid:=…]> es1)] subgoal open so the
    caller discharges it with whatever wf-preservation argument fits. *)
Ltac close_ext_pure :=
  iPureIntro; unfold mirror_ok; split;
  [ constructor; try done;
    [ rewrite length_insert; done | apply Forall_insert; first done ]
  | try assumption ].

(** [heap_partition] is preserved by writing to an already-allocated key:
    headers and the heap domain are unchanged, and the value at a present
    key does not affect [is_Some]. *)
Lemma heap_partition_set_location k w σ :
  k ∈ dom σ.(state_heap) →
  heap_partition σ →
  heap_partition (state_set_location k w σ).
Proof.
  intros Hk (Hc & Hcov & Hd).
  rewrite /heap_partition /state_set_location /state_update_heap /=.
  split_and!.
  - intros l hdr Hl i Hi. destruct (Hc l hdr Hl i Hi) as [v Hv].
    destruct (decide (l +ₗ Z.of_nat i = k)) as [->|Hne];
      [rewrite lookup_insert_eq | rewrite lookup_insert_ne //]; by eexists.
  - intros j Hj. rewrite dom_insert_L in Hj.
    apply elem_of_union in Hj as [Hj|Hj].
    + apply elem_of_singleton in Hj as ->. by apply Hcov.
    + by apply Hcov.
  - exact Hd.
Qed.

(** Closing tactic for cases that write a single new value into [state_heap]
    at an already-allocated key. Leaves the [Forall wf_expr] and the
    [map_Forall wf_val] subgoals open for case-specific reasoning. *)
Ltac close_ext_heap_store :=
  iPureIntro; unfold mirror_ok; split; [| try assumption];
  constructor; simpl;
  [ done
  | rewrite length_insert //
  | erewrite dom_insert_lookup_L; eauto
  | done
  | erewrite dom_insert_lookup_L; eauto
  | erewrite dom_insert_lookup_L; eauto
  | done
  | (* wfes *) idtac
  | done
  | (* wfhp *) idtac
  | done
  | apply heap_partition_set_location; [apply elem_of_dom; eauto | eauto] ].

(** [orphan_headers] is preserved by inserting into the heap at an
    already-allocated key. *)
Lemma orphan_headers_heap_insert l v σ :
  l ∈ dom σ.(state_heap) →
  orphan_headers {| state_headers := σ.(state_headers);
                    state_heap := <[l := v]> σ.(state_heap);
                    state_locals := σ.(state_locals) |}
   = orphan_headers σ.
Proof.
  intros Hin. rewrite /orphan_headers /=. rewrite dom_insert_L. set_solver.
Qed.

(** Discharge the [wf_expr ψ (fill K e2')] subgoal in pure-step cases.
    Requires [Hwfes] and [Hlook] in scope, and that
    [locs_expr e2' ⊆ locs_expr e1'] is solvable by [simpl] + [set_solver]. *)
Ltac solve_wf_pure :=
  match goal with
  | Hwfes : Forall (wf_expr _) _, Hlook : _ !! _ = Some _ |- _ =>
      eapply wf_fill_mono;
        [|eapply (Forall_lookup_1 _ _ _ _ Hwfes Hlook)];
      simpl; try set_solver
  end.

#[local] Lemma big_sepL2_insert_r' `{!BiAffine PROP} {A B : Type}
    (Φ : nat → A → B → PROP) (l1 : list A) (l2 : list B)
    (i : nat) (x1 : A) (x2 : B) :
  l1 !! i = Some x1 →
  i < length l2 →
  Φ i x1 x2 -∗
  ([∗ list] k↦y1;y2 ∈ l1; l2, ⌜k ≠ i⌝ → Φ k y1 y2) -∗
  [∗ list] k↦y1;y2 ∈ l1; <[i:=x2]> l2, Φ k y1 y2.
Proof.
  iIntros (Hlook Hlen) "HΦ Hbig".
  iInduction l1 as [|a xs IH] forall (Φ l2 i x1 Hlook Hlen).
  - simpl in Hlook. done.
  - destruct l2 as [|b ys]; first by (simpl in Hlen; lia).
    destruct i as [|i'].
    + simpl in Hlook. injection Hlook as ->.
      simpl. iDestruct "Hbig" as "[_ Hbig]".
      iFrame "HΦ".
      iApply (big_sepL2_mono with "Hbig").
      intros k y1 y2 Hk Hy. iIntros "H". iApply "H". iPureIntro. lia.
    + simpl in Hlook. simpl in Hlen.
      simpl. iDestruct "Hbig" as "[H Hbig]".
      iSplitL "H".
      { iApply "H". iPureIntro. lia. }
      iApply ("IH" $! (λ k y1 y2, Φ (S k) y1 y2) ys i' x1 with "[%] [%] HΦ [Hbig]"); [done|lia|].
      iApply (big_sepL2_mono with "Hbig"). intros k y1 y2 Hk Hy. simpl.
      iIntros "H" (Hne). iApply "H". iPureIntro. lia.
Qed.

(** Extending an injective [ψ] with a fresh block [(l, l'), (l+1, l'+1), …, (l+n-1, l'+n-1)]
    preserves injectivity, provided no existing image of [ψ] hits any of the new
    target locations [l' +ₗ i] (i < n) or [l'] itself. *)
Lemma tr_inj_alloc (ψ : gmap location location) (l l' : location) (n : nat) :
  tr_inj ψ ->
  (∀ l0 v, ψ !! l0 = Some v → v ≠ l') ->
  (∀ i, (i < n)%nat → ∀ l0 v, ψ !! l0 = Some v → v ≠ l' +ₗ Z.of_nat i) ->
  tr_inj (<[l := l']>
            (list_to_map ((λ i, (l +ₗ Z.of_nat i, l' +ₗ Z.of_nat i)) <$> seq 0 n)
             ∪ ψ)).
Proof.
  intros Hinj Hcodom_fresh0 Hcodom_fresh k1 k2 v Hk1 Hk2.
  set (ψ' := <[l := l']>
               (list_to_map ((λ i, (l +ₗ Z.of_nat i, l' +ₗ Z.of_nat i)) <$> seq 0 n)
                ∪ ψ)).
  assert (Hcase : ∀ k v',
            ψ' !! k = Some v' →
            (k = l ∧ v' = l')
            ∨ (∃ i, (i < n)%nat ∧ k = l +ₗ Z.of_nat i ∧ v' = l' +ₗ Z.of_nat i)
            ∨ ψ !! k = Some v').
  { intros k v' Hk.
    rewrite /ψ' lookup_insert_Some in Hk.
    destruct Hk as [[-> ->]|[_ Hk]]; first by left.
    rewrite lookup_union_Some_raw in Hk.
    destruct Hk as [Hk|[_ Hk]]; last (right; by right).
    apply elem_of_list_to_map_2 in Hk.
    apply list_elem_of_fmap in Hk as [i [Heq Hi]]. simpl in Heq.
    injection Heq as -> ->.
    apply elem_of_seq in Hi as [_ Hilt].
    right; left. exists i. done. }
  destruct (Hcase _ _ Hk1) as [[-> ->] | [(i1 & Hi1 & -> & ->) | Hψ1]];
  destruct (Hcase _ _ Hk2) as [[-> Hv] | [(i2 & Hi2 & -> & Heq) | Hψ2]].
  - done.
  - assert (Z.of_nat i2 = 0%Z) as Hi2eq.
    { apply (inj (location_add l')).
      rewrite location_add_0. by symmetry. }
    rewrite Hi2eq location_add_0 //.
  - exfalso. by eapply Hcodom_fresh0.
  - assert (Z.of_nat i1 = 0%Z) as Hi1eq.
    { apply (inj (location_add l')).
      rewrite location_add_0. exact Hv. }
    rewrite Hi1eq location_add_0 //.
  - apply (inj (location_add l')) in Heq.
    apply Nat2Z.inj in Heq. by rewrite Heq.
  - exfalso. by eapply (Hcodom_fresh _ Hi1 _ _ Hψ2).
  - exfalso. by eapply Hcodom_fresh0.
  - exfalso. by eapply (Hcodom_fresh _ Hi2 _ _ Hψ1).
  - eapply Hinj; eauto.
Qed.

(** Block-alignment of [tr_loc]. Holds whenever [ψ] maps the contiguous
    pair [(l, l +ₗ fld)] block-consistently — i.e. the same offset applies
    on both sides. Discharged at call sites via [ei_block]. *)
Lemma tr_loc_offset (ψ : gmap location location) l l' (fld : Z) :
  ψ !! l = Some l' →
  ψ !! (l +ₗ fld) = Some (l' +ₗ fld) →
  tr_loc ψ (l +ₗ fld) = tr_loc ψ l +ₗ fld.
Proof. intros H1 H2. rewrite /tr_loc H1 /= H2 //=. Qed.

(** From block alignment + an in-bounds header lookup at [l], derive the
    [ψ]-witness that justifies [tr_loc_offset] at offset [fld]. *)
Lemma block_witness σ ψ (l : location) (fld : Z) :
  block_aligned ψ σ →
  (∃ hdr, σ.(state_headers) !! l = Some hdr ∧
          (0 ≤ fld < Z.of_nat (header_size hdr))%Z) →
  ∃ l_img, ψ !! l = Some l_img ∧
           ψ !! (l +ₗ fld) = Some (l_img +ₗ fld).
Proof.
  intros Hblk (hdr & Hhdr & Hlo & Hhi).
  assert (Hi : (Z.to_nat fld < header_size hdr)%nat) by lia.
  destruct (Hblk _ _ Hhdr _ Hi) as (l_img & Hψl & Hψlf).
  rewrite Z2Nat.id in Hψlf; [|lia].
  by exists l_img.
Qed.


(** Translation map extended with a fresh block of [n] cells starting at
    [l ↦ l']. Offset-by-offset: [l +ₗ i ↦ l' +ₗ i]. Entries outside the
    block are inherited from [ψ]. *)
Definition ψ_alloc (ψ : gmap location location)
                   (l l' : location) (n : nat) : gmap location location :=
  <[l := l']>
    (list_to_map ((λ i, (l +ₗ Z.of_nat i, l' +ₗ Z.of_nat i)) <$> seq 0 n)
     ∪ ψ).

Lemma ψ_alloc_lookup_l ψ l l' n : ψ_alloc ψ l l' n !! l = Some l'.
Proof. by rewrite /ψ_alloc lookup_insert_eq. Qed.

Lemma ψ_alloc_lookup_new ψ l l' n i :
  (i < n)%nat →
  ψ_alloc ψ l l' n !! (l +ₗ Z.of_nat i) = Some (l' +ₗ Z.of_nat i).
Proof.
  intros Hi.
  destruct (decide (i = 0)) as [->|Hne].
  { rewrite Nat2Z.inj_0 !location_add_0. apply ψ_alloc_lookup_l. }
  rewrite /ψ_alloc lookup_insert_ne.
  2:{ intros Heq. apply Hne. rewrite -(location_add_0 l) in Heq.
      rewrite location_add_assoc in Heq.
      apply (inj (location_add l)) in Heq. lia. }
  rewrite lookup_union_with.
  assert (Hlookup :
    (list_to_map ((λ j, (l +ₗ Z.of_nat j, l' +ₗ Z.of_nat j)) <$> seq 0 n)
       : gmap location location)
    !! (l +ₗ Z.of_nat i) = Some (l' +ₗ Z.of_nat i)).
  { apply elem_of_list_to_map_1.
    { rewrite -list_fmap_compose. apply NoDup_fmap_2; last apply NoDup_seq.
      intros j k Hjk. simpl in Hjk. apply (inj (location_add l)) in Hjk. lia. }
    rewrite list_elem_of_fmap. exists i. split; first done.
    apply elem_of_seq. lia. }
  rewrite Hlookup. destruct (ψ !! _); reflexivity.
Qed.

Lemma ψ_alloc_lookup_old ψ l l' n k :
  l ∉ dom ψ →
  (∀ i, (i < n)%nat → l +ₗ Z.of_nat i ∉ dom ψ) →
  k ∈ dom ψ →
  ψ_alloc ψ l l' n !! k = ψ !! k.
Proof.
  intros Hl Hi Hk.
  rewrite /ψ_alloc lookup_insert_ne; last by (intros ->; congruence).
  rewrite lookup_union_with.
  assert (Hnone :
    (list_to_map ((λ j, (l +ₗ Z.of_nat j, l' +ₗ Z.of_nat j)) <$> seq 0 n)
       : gmap location location) !! k = None).
  { apply not_elem_of_list_to_map_1. intros Hin.
    rewrite -list_fmap_compose in Hin.
    apply list_elem_of_fmap in Hin as [j [Heq Hjlt]]; simpl in Heq; subst k.
    apply elem_of_seq in Hjlt as [_ Hjlt].
    by apply (Hi j Hjlt). }
  rewrite Hnone. destruct (ψ !! k); reflexivity.
Qed.

(** Key building block for [tr_inj_alloc]'s freshness premises. *)
Lemma mirror_loc_tok_excluded ψ σ l0 m :
  dom ψ ⊆ dom σ.(state_heap) ∪ dom σ.(state_headers) →
  ψ !! l0 = Some m →
  ([∗ map] l ↦ v ∈ σ.(state_heap), tr_loc ψ l ↦ tr_val ψ v) -∗
  ([∗ set] l ∈ orphan_headers σ, loc_tok1 (tr_loc ψ l)) -∗
  loc_tok1 m -∗
  False.
Proof.
  intros Hdomψ Hψl0.
  iIntros "Hheap Horphans Htok".
  assert (Htr : tr_loc ψ l0 = m) by (rewrite /tr_loc Hψl0 //).
  assert (l0 ∈ dom ψ) as Hl0_dom by (apply elem_of_dom; eauto).
  apply Hdomψ in Hl0_dom.
  destruct (decide (l0 ∈ dom σ.(state_heap))) as [Hl0_h | Hl0_nh].
  - apply elem_of_dom in Hl0_h as [v0 Hv0].
    iDestruct (big_sepM_lookup with "Hheap") as "[_ Htok']"; first exact Hv0.
    rewrite Htr.
    iApply (loc_tok1_exclusive with "Htok' Htok").
  - assert (Hl0_orph : l0 ∈ orphan_headers σ).
    { rewrite /orphan_headers. apply elem_of_difference. split; last done.
      apply elem_of_union in Hl0_dom as [|]; [done|done]. }
    iDestruct (big_sepS_elem_of with "Horphans") as "Htok'"; first exact Hl0_orph.
    rewrite Htr.
    iApply (loc_tok1_exclusive with "Htok' Htok").
Qed.

(** [chunk l vs] is disjoint from the state's headers as long as each cell
    address is fresh in the headers map. Used to split the post-allocation
    heap [big_sepM] and to compute the new orphan set. *)
Lemma chunk_disj_state_headers σ (l : location) (vs : list val) :
  (∀ i, (i < length vs)%nat → state_headers σ !! (l +ₗ i) = None) →
  dom (chunk l vs) ## dom σ.(state_headers).
Proof.
  intros Hno_h. apply elem_of_disjoint. intros k [w Hk]%elem_of_dom Hin.
  apply chunk_lookup in Hk as (j & Hj0 & -> & Hjvs).
  apply lookup_lt_Some in Hjvs.
  ospecialize (Hno_h (Z.to_nat j) _); first lia.
  rewrite Z2Nat.id in Hno_h; last lia.
  apply elem_of_dom in Hin as [? Hx]. congruence.
Qed.

(** Propositional core of the allocator-shape step rules:
    extending [ψ] to [ψ_alloc ψ l l' (length vs)] preserves
    [mirror_invs] when stepping into the post-allocation state. *)
Lemma mirror_invs_alloc
    φ ψ es1 σ1 tid K e_src tag (vs : list val) (l l' : location) :
  mirror_invs φ ψ es1 σ1 →
  es1 !! tid = Some (fill K e_src) →
  Forall (wf_val ψ) vs →
  state_headers σ1 !! l = None →
  state_heap σ1 !! l = None →
  (∀ i, (i < length vs)%nat →
     state_headers σ1 !! (l +ₗ i) = None ∧
     state_heap σ1 !! (l +ₗ i) = None) →
  (∀ l0 v, ψ !! l0 = Some v → v ≠ l') →
  (∀ i, (i < length vs)%nat → ∀ l0 v, ψ !! l0 = Some v → v ≠ l' +ₗ Z.of_nat i) →
  mirror_invs φ (ψ_alloc ψ l l' (length vs))
                (<[tid := fill K #l]> es1)
                (state_alloc l (Header tag (length vs)) vs σ1).
Proof.
  intros Hinv Hlook Hwf_vs H1 Hheap_l H2 Hcodom_fresh0 Hcodom_fresh.
  destruct Hinv as [Hnd Hlen Hdomh Hdomhd Hdomψ Hcodomψ Hinj Hwfes Hwfls Hwfhp Hblock Hpart].
  pose proof (Forall_lookup_1 _ _ _ _ Hwfes Hlook) as Hwf_e.
  apply wf_fill in Hwf_e as [HKwf _].
  set (ψ' := ψ_alloc ψ l l' (length vs)).
  assert (Hl_fresh : ∀ i, (i < length vs)%nat → l +ₗ Z.of_nat i ∉ dom ψ).
  { intros i Hi Hin. apply Hdomψ in Hin.
    destruct (H2 i Hi) as [Hhd Hhp].
    apply elem_of_union in Hin as [Hin|Hin];
      apply elem_of_dom in Hin as [? Hx]; simpl in *; congruence. }
  assert (Hl_fresh0 : l ∉ dom ψ).
  { intros Hin. apply Hdomψ in Hin.
    apply elem_of_union in Hin as [Hin|Hin];
      apply elem_of_dom in Hin as [? Hx]; simpl in *; congruence. }
  assert (Hψ_old : ∀ k, k ∈ dom (state_heap σ1) ∨ k ∈ dom (state_headers σ1) → ψ' !! k = ψ !! k).
  { intros k Hk. apply ψ_alloc_lookup_old; auto.
    destruct Hk as [Hk|Hk]; [by apply Hdomh|by apply Hdomhd]. }
  assert (Hψ'_new : ∀ i, (i < length vs)%nat → ψ' !! (l +ₗ Z.of_nat i) = Some (l' +ₗ Z.of_nat i)).
  { apply ψ_alloc_lookup_new. }
  assert (Hψ'_l : ψ' !! l = Some l') by apply ψ_alloc_lookup_l.
  assert (Htr_loc_old : ∀ k, k ∈ dom (state_heap σ1) ∨ k ∈ dom (state_headers σ1) → tr_loc ψ' k = tr_loc ψ k).
  { intros k Hk. rewrite /tr_loc Hψ_old //. }
  assert (Htr_loc_new : ∀ i, (i < length vs)%nat → tr_loc ψ' (l +ₗ Z.of_nat i) = l' +ₗ Z.of_nat i).
  { intros i Hi. rewrite /tr_loc Hψ'_new //. }
  assert (Htr_loc_l : tr_loc ψ' l = l') by (rewrite /tr_loc Hψ'_l //).
  assert (Hdom_sub : dom ψ ⊆ dom ψ').
  { rewrite /ψ' /ψ_alloc dom_insert_L dom_union_L. set_solver. }
  assert (Hinj' : tr_inj ψ').
  { rewrite /ψ' /ψ_alloc. by apply tr_inj_alloc. }
  constructor.
  - done.
  - rewrite /= /state_alloc /= length_insert //.
  - simpl. rewrite /state_alloc /= dom_union_L.
    apply union_subseteq. split.
    + intros k Hk. apply elem_of_dom in Hk as [w Hk].
      apply chunk_lookup in Hk as (j & Hj0 & -> & Hjvs).
      apply lookup_lt_Some in Hjvs.
      apply elem_of_dom. exists (l' +ₗ j).
      pose proof (Hψ'_new (Z.to_nat j) Hjvs) as Hp.
      rewrite Z2Nat.id in Hp; [exact Hp|lia].
    + intros l0 Hl0. apply elem_of_dom in Hl0 as [v Hv].
      apply elem_of_dom. rewrite Hψ_old.
      * apply elem_of_dom. apply Hdomh. apply elem_of_dom. by eexists.
      * left; by apply elem_of_dom.
  - simpl. rewrite /state_alloc /= dom_insert_L.
    apply union_subseteq. split.
    + apply singleton_subseteq_l. apply elem_of_dom. eauto.
    + intros l0 Hl0. apply elem_of_dom in Hl0 as [hd Hv].
      apply elem_of_dom. rewrite Hψ_old.
      * apply elem_of_dom. apply Hdomhd. apply elem_of_dom. by eexists.
      * right; by apply elem_of_dom.
  - simpl. rewrite /state_alloc /=.
    rewrite dom_union_L dom_insert_L.
    intros k Hk. rewrite /ψ' /ψ_alloc in Hk. rewrite dom_insert_L in Hk.
    apply elem_of_union in Hk as [Hk|Hk].
    + apply elem_of_singleton in Hk; subst k. set_solver.
    + rewrite dom_union_L in Hk.
      apply elem_of_union in Hk as [Hk|Hk].
      * apply elem_of_dom in Hk as [v Hv].
        apply elem_of_list_to_map_2 in Hv.
        apply list_elem_of_fmap in Hv as [i [Heq Hi]]. simpl in Heq.
        injection Heq as -> _.
        apply elem_of_seq in Hi as [_ Hilt].
        apply elem_of_union_l, elem_of_union_l.
        apply elem_of_dom.
        destruct (lookup_lt_is_Some_2 vs i Hilt) as [vi Hvi].
        exists vi.
        apply chunk_lookup. exists (Z.of_nat i). split_and!; [lia|done|].
        rewrite Nat2Z.id //.
      * apply Hdomψ in Hk. set_solver.
  - simpl. rewrite /state_alloc /=.
    intros z Hz. apply elem_of_map_img in Hz as [k0 Hk0].
    rewrite /ψ' /ψ_alloc lookup_insert_Some in Hk0.
    destruct Hk0 as [[Heqk Heqv]|[Hne Hk0]].
    { subst k0. subst z. apply elem_of_map. exists l. split; [done|].
      apply elem_of_union_r. rewrite dom_insert_L. set_solver. }
    rewrite lookup_union_Some_raw in Hk0.
    destruct Hk0 as [Hk0|[Hnone Hk0]].
    + apply elem_of_list_to_map_2 in Hk0.
      apply list_elem_of_fmap in Hk0 as [i [Heq Hi]]. simpl in Heq.
      injection Heq as -> ->.
      apply elem_of_seq in Hi as [_ Hilt].
      apply elem_of_map. exists (l +ₗ Z.of_nat i). split.
      * rewrite Htr_loc_new //.
      * apply elem_of_union_l. apply elem_of_dom.
        destruct (lookup_lt_is_Some_2 vs i Hilt) as [vi Hvi].
        exists vi.
        apply lookup_union_Some_l.
        apply chunk_lookup. exists (Z.of_nat i). split_and!; [lia|done|].
        rewrite Nat2Z.id //.
    + ospecialize* Hcodomψ.
      { apply elem_of_map_img. exists k0. done. }
      apply elem_of_map in Hcodomψ as [k' [-> Hk']].
      apply elem_of_map. exists k'. split.
      * symmetry. apply Htr_loc_old. set_solver.
      * apply elem_of_union in Hk' as [Hk'|Hk'].
        -- apply elem_of_union_l. rewrite dom_union_L. set_solver.
        -- apply elem_of_union_r. rewrite dom_insert_L. set_solver.
  - done.
  - apply Forall_insert.
    { apply (Forall_impl _ _ _ Hwfes).
      intros e He. eapply wf_expr_mono; eauto. }
    apply wf_fill. split.
    + set_solver.
    + rewrite /wf_expr /=. intros k Hk.
      rewrite elem_of_singleton in Hk. subst k.
      apply elem_of_dom. eauto.
  - simpl. rewrite /state_alloc /=.
    apply (Forall_impl _ _ _ Hwfls).
    intros v Hv. eapply wf_val_mono; eauto.
  - simpl. rewrite /state_alloc /=.
    apply map_Forall_union_2.
    + intros k v Hkv. apply chunk_lookup in Hkv as (i & Hi & _ & Hri).
      eapply wf_val_mono; first exact Hdom_sub.
      rewrite Forall_forall in Hwf_vs. apply Hwf_vs.
      eapply list_elem_of_lookup_2; eauto.
    + eapply map_Forall_impl; first exact Hwfhp.
      intros k v Hv. simpl in Hv. eapply wf_val_mono; eauto.
  - simpl. rewrite /state_alloc /=.
    intros l0 hdr Hl0 i Hi.
    rewrite lookup_insert_Some in Hl0.
    destruct Hl0 as [[<- <-]|[Hne Hl0]].
    + simpl in Hi.
      exists l'. split; first exact Hψ'_l.
      by apply Hψ'_new.
    + assert (Hl0_dom : l0 ∈ dom σ1.(state_headers))
        by (apply elem_of_dom; eauto).
      destruct (Hblock _ _ Hl0 _ Hi) as (l'' & Hψl0 & Hψl0i).
      exists l''. split.
      * rewrite Hψ_old; [exact Hψl0|by right].
      * rewrite Hψ_old; first exact Hψl0i.
        assert (l0 +ₗ Z.of_nat i ∈ dom ψ) as Hin by (apply elem_of_dom; eauto).
        apply Hdomψ in Hin. apply elem_of_union in Hin as [Hin|Hin]; auto.
  - (* heap_partition *)
    destruct Hpart as (Hcompl & Hcov & Hdisj).
    assert (Hchunk_disj : chunk l vs ##ₘ σ1.(state_heap)).
    { apply chunk_map_disjoint. intros i Hi. apply (H2 i Hi). }
    rewrite /heap_partition /= /state_alloc /=. split_and!.
    + (* completeness *)
      intros l0 hdr Hl0 i Hi.
      rewrite lookup_insert_Some in Hl0.
      destruct Hl0 as [[<- <-]|[Hne Hl0]].
      * simpl in Hi.
        destruct (lookup_lt_is_Some_2 vs i Hi) as [vi Hvi].
        exists vi. apply lookup_union_Some_l.
        apply chunk_lookup. exists (Z.of_nat i). rewrite Nat2Z.id. split_and!; [lia|done|done].
      * destruct (Hcompl _ _ Hl0 _ Hi) as [w Hw].
        exists w. by apply lookup_union_Some_r.
    + (* covered *)
      intros k Hk. rewrite dom_union_L in Hk. apply elem_of_union in Hk as [Hk|Hk].
      * apply elem_of_dom in Hk as [w Hw].
        apply chunk_lookup in Hw as (j & Hj0 & -> & Hjvs).
        exists l, (Header tag (length vs)), (Z.to_nat j). split_and!.
        -- apply lookup_insert_eq.
        -- simpl. apply lookup_lt_Some in Hjvs. lia.
        -- rewrite Z2Nat.id //.
      * destruct (Hcov _ Hk) as (l0 & hdr & i & Hl0 & Hi & ->).
        exists l0, hdr, i. split_and!; [|done|done].
        rewrite lookup_insert_ne; [done|].
        intros <-. rewrite H1 in Hl0. discriminate.
    + (* disjoint *)
      intros l1 h1 l2 h2 i1 i2 Hl1 Hl2 Hi1 Hi2 Heq.
      rewrite lookup_insert_Some in Hl1.
      rewrite lookup_insert_Some in Hl2.
      destruct Hl1 as [[<- <-]|[Hne1 Hl1]]; destruct Hl2 as [[<- <-]|[Hne2 Hl2]].
      * split; first done. apply (inj (location_add l)) in Heq. lia.
      * exfalso. simpl in Hi1. destruct (H2 i1 Hi1) as [_ Hn].
        rewrite Heq in Hn. destruct (Hcompl _ _ Hl2 _ Hi2) as [w Hw].
        rewrite Hw in Hn. discriminate.
      * exfalso. simpl in Hi2. destruct (H2 i2 Hi2) as [_ Hn].
        rewrite -Heq in Hn. destruct (Hcompl _ _ Hl1 _ Hi1) as [w Hw].
        rewrite Hw in Hn. discriminate.
      * eapply Hdisj; eauto.
Qed.

(** Resource side of the allocator-shape step: assemble the post-step
    [mirror] from the destructured pre-step resources and the
    post-allocation tokens (header, cells in canonical form, optional
    orphan token). Calls [mirror_invs_alloc] for the propositional
    invariant. *)
Lemma mirror_resources_alloc
    φ ψ es1 σ1 tid pid K e_src vloc tag (vs : list val) (l l' : location)
    (κ : list observation) :
  mirror_invs φ ψ es1 σ1 →
  trace_wf ψ κ →
  φ !! tid = Some pid →
  state_locals σ1 !! tid = Some vloc →
  es1 !! tid = Some (fill K e_src) →
  Forall (wf_val ψ) vs →
  state_headers σ1 !! l = None →
  state_heap σ1 !! l = None →
  (∀ i, (i < length vs)%nat →
     state_headers σ1 !! (l +ₗ i) = None ∧
     state_heap σ1 !! (l +ₗ i) = None) →
  (∀ l0 v, ψ !! l0 = Some v → v ≠ l') →
  (∀ i, (i < length vs)%nat → ∀ l0 v, ψ !! l0 = Some v → v ≠ l' +ₗ Z.of_nat i) →
  ([∗ list] k↦y1;y2 ∈ φ;es1, ⌜k ≠ tid⌝ → running y1 (tr_expr ψ y2)) -∗
  ([∗ list] y0;y3 ∈ φ;state_locals σ1, local y0 (tr_val ψ y3)) -∗
  ([∗ map] l0↦v ∈ state_heap σ1, tr_loc ψ l0 ↦ tr_val ψ v) -∗
  ([∗ map] l0↦h ∈ state_headers σ1, tr_loc ψ l0 ↦ₕ□ h) -∗
  ([∗ set] l0 ∈ orphan_headers σ1, loc_tok1 (tr_loc ψ l0)) -∗
  l' ↦ₕ□ Header tag (length vs) -∗
  ([∗ list] i ↦ v ∈ vs, (l' +ₗ Z.of_nat i) ↦ tr_val ψ v) -∗
  (⌜(length vs = 0)%nat⌝ -∗ loc_tok1 l') -∗
  trace_model (tr_val ψ <$> κ) -∗
  running pid (fill (tr_ectx ψ K) #l') -∗
  mirror (<[tid := fill K #l]> es1)
           (state_alloc l (Header tag (length vs)) vs σ1) κ.
Proof.
  intros Hinv Hpwf Hpid Hvloc Hlook Hwf_vs H1 Hheap_l H2 Hcodom_fresh0 Hcodom_fresh.
  iIntros "Hes Hloc Hheap Hhdrs Horphans Hhdr' Hcells' Horph Hpm Hrun".
  pose proof Hinv as Hinv'.
  destruct Hinv' as [Hnd Hlen Hdomh Hdomhd Hdomψ Hcodomψ Hinj Hwfes Hwfls Hwfhp Hblock Hpart].
  pose proof Hlook as Hlook'.
  apply lookup_lt_Some in Hlook'.
  pose proof (Forall_lookup_1 _ _ _ _ Hwfes Hlook) as Hwf_e.
  apply wf_fill in Hwf_e as [HKwf _].
  set (ψ' := ψ_alloc ψ l l' (length vs)).
  assert (Hl_fresh0 : l ∉ dom ψ).
  { intros Hin. apply Hdomψ in Hin.
    apply elem_of_union in Hin as [Hin|Hin];
      apply elem_of_dom in Hin as [? Hx]; simpl in *; congruence. }
  assert (Hl_fresh : ∀ i, (i < length vs)%nat → l +ₗ Z.of_nat i ∉ dom ψ).
  { intros i Hi Hin. apply Hdomψ in Hin.
    destruct (H2 i Hi) as [Hhd Hhp].
    apply elem_of_union in Hin as [Hin|Hin];
      apply elem_of_dom in Hin as [? Hx]; simpl in *; congruence. }
  assert (Hψ_old : ∀ k, k ∈ dom (state_heap σ1) ∨ k ∈ dom (state_headers σ1) → ψ' !! k = ψ !! k).
  { intros k Hk. apply ψ_alloc_lookup_old; auto.
    destruct Hk as [Hk|Hk]; [by apply Hdomh|by apply Hdomhd]. }
  assert (Hψ'_new : ∀ i, (i < length vs)%nat → ψ' !! (l +ₗ Z.of_nat i) = Some (l' +ₗ Z.of_nat i)).
  { apply ψ_alloc_lookup_new. }
  assert (Hψ'_l : ψ' !! l = Some l') by apply ψ_alloc_lookup_l.
  assert (Htr_loc_old : ∀ k, k ∈ dom (state_heap σ1) ∨ k ∈ dom (state_headers σ1) → tr_loc ψ' k = tr_loc ψ k).
  { intros k Hk. rewrite /tr_loc Hψ_old //. }
  assert (Htr_loc_new : ∀ i, (i < length vs)%nat → tr_loc ψ' (l +ₗ Z.of_nat i) = l' +ₗ Z.of_nat i).
  { intros i Hi. rewrite /tr_loc Hψ'_new //. }
  assert (Htr_loc_l : tr_loc ψ' l = l') by (rewrite /tr_loc Hψ'_l //).
  assert (Hagree : ∀ k, k ∈ dom ψ → ψ' !! k = ψ !! k).
  { intros k Hk. apply Hψ_old. apply Hdomψ in Hk.
    apply elem_of_union in Hk as [Hk|Hk]; auto. }
  assert (Hdomsub : dom ψ ⊆ dom ψ').
  { intros k Hk. apply elem_of_dom. rewrite (Hagree k Hk). by apply elem_of_dom. }
  rewrite mirror_unfold.
  iExists φ, ψ'.
  rewrite (tr_trace_extend ψ ψ' κ Hagree Hpwf).
  iFrame "Hpm".
  iSplitR.
  { iPureIntro. split.
    { by apply (mirror_invs_alloc φ ψ es1 σ1 tid K e_src tag vs l l'). }
    { by apply (trace_wf_mono ψ ψ'). } }
  iSplitL "Hrun Hes".
  { iApply (big_sepL2_delete' _ _ _ tid); first done.
    { rewrite list_lookup_insert decide_True //. }
    iSplitL "Hrun".
    { rewrite tr_fill. simpl. rewrite Htr_loc_l.
      rewrite (tr_ectx_extend ψ ψ' K Hagree HKwf). done. }
    { iApply big_sepL2_insert_r'. 1,2:done. 1:by iIntros.
      iApply (big_sepL2_impl with "Hes").
      iModIntro. iIntros (k x1 x2 Hk Hx2) "Hbody".
      iIntros (Hne _).
      iSpecialize ("Hbody" $! Hne).
      rewrite (tr_expr_extend ψ ψ' x2 Hagree).
      { iFrame. }
      eapply (Forall_lookup_1 _ _ _ _ Hwfes Hx2). } }
  iSplitL "Hloc".
  { iApply (big_sepL2_impl with "Hloc").
    iModIntro. iIntros (k x1 x2 Hk Hsk1) "Hloc".
    rewrite (tr_val_extend ψ ψ' x2 Hagree).
    { iFrame. }
    eapply (Forall_lookup_1 _ _ _ _ Hwfls Hsk1). }
  iSplitL "Hheap Hcells'".
  { simpl. rewrite /state_alloc /=.
    rewrite big_sepM_union; last first.
    { apply chunk_map_disjoint. intros i Hi. apply (H2 i Hi). }
    iSplitL "Hcells'".
    - iAssert ([∗ list] i ↦ v ∈ vs,
                tr_loc ψ' (l +ₗ i) ↦ tr_val ψ' v)%I with "[Hcells']" as "Hcells'".
      { iApply (big_sepL_mono with "Hcells'"). intros k v Hk.
        rewrite Htr_loc_new; last by eapply lookup_lt_Some.
        rewrite (tr_val_extend ψ ψ' v Hagree); first done.
        rewrite Forall_forall in Hwf_vs.
        apply Hwf_vs. eapply list_elem_of_lookup_2; eauto. }
      iApply big_sepL_heap_array. iApply "Hcells'".
    - iApply (big_sepM_mono with "Hheap"). intros k v Hkv.
      rewrite Htr_loc_old; last by (left; apply elem_of_dom; eauto).
      rewrite (tr_val_extend ψ ψ' v Hagree); first done.
      eapply Hwfhp; eauto. }
  iSplitL "Hhdr' Hhdrs".
  { simpl. rewrite /state_alloc /=.
    rewrite big_sepM_insert; last by apply H1.
    iSplitL "Hhdr'".
    - rewrite Htr_loc_l. done.
    - iApply (big_sepM_mono with "Hhdrs"). intros k v Hkv.
      rewrite Htr_loc_old; last by (right; apply elem_of_dom; eauto).
      done. }
  (* Orphan-header tokens: split on whether the new block is size-0. *)
  rewrite /orphan_headers /state_alloc /=.
  rewrite dom_insert_L dom_union_L.
  assert (Hl_not_old_h : l ∉ dom σ1.(state_headers)).
  { intros [v Hv]%elem_of_dom. congruence. }
  assert (Hl_not_old_heap : l ∉ dom σ1.(state_heap)).
  { intros [v Hv]%elem_of_dom. congruence. }
  destruct (decide ((length vs = 0)%nat)) as [Hzn|Hzn].
  - (* size-0: l becomes a new orphan; consume [Horph]. *)
    apply nil_length_inv in Hzn. subst vs. simpl.
    rewrite dom_empty_L union_empty_l_L.
    iSpecialize ("Horph" with "[//]").
    replace (({[l]} ∪ dom σ1.(state_headers))
              ∖ (dom σ1.(state_heap)))
      with ({[l]} ∪ orphan_headers σ1)
      by (rewrite /orphan_headers; set_solver).
    rewrite big_sepS_insert; last by rewrite /orphan_headers; set_solver.
    iSplitL "Horph".
    + rewrite Htr_loc_l. iFrame.
    + iApply (big_sepS_mono with "Horphans"). intros l0 Hl0.
      rewrite /orphan_headers in Hl0.
      assert (Hl0_in_hd : l0 ∈ dom σ1.(state_headers)) by set_solver.
      rewrite Htr_loc_old; first done. by right.
  - (* non-empty: orphan set unchanged; [Horph] discarded. *)
    assert (Hpos : (0 < length vs)%nat) by lia.
    assert (Hl_in_chunk : l ∈ dom (chunk l vs)).
    { destruct vs as [|v0 vs']; first (simpl in Hpos; lia).
      apply elem_of_dom. exists v0.
      apply chunk_lookup. exists 0%Z. split_and!; [lia| |].
      - by rewrite location_add_0.
      - reflexivity. }
    pose proof (chunk_disj_state_headers σ1 l vs (λ i Hi, proj1 (H2 i Hi))) as Hchunk_disj.
    replace (({[l]} ∪ dom σ1.(state_headers))
              ∖ (dom (chunk l vs) ∪ dom σ1.(state_heap)))
      with (orphan_headers σ1)
      by (rewrite /orphan_headers; set_solver).
    iApply (big_sepS_mono with "Horphans"). intros l0 Hl0.
    rewrite /orphan_headers in Hl0.
    assert (Hl0_in_hd : l0 ∈ dom σ1.(state_headers)) by set_solver.
    rewrite Htr_loc_old; first done. by right.
Qed.

Lemma update_mirror_step_alloc (E : coPset) (es1 : list expr) (σ1 : state)
  (κ : list observation)
  (tid : nat) (K : ectx) (tag : nat) (n : Z) (l : location) :
  es1 !! tid = Some (fill K (Alloc #tag #n)) ->
  (0 ≤ n)%Z ->
  state_headers σ1 !! l = None ->
  state_heap σ1 !! l = None ->
  (∀ i, (i < Z.to_nat n)%nat →
     state_headers σ1 !! (l +ₗ i) = None ∧
     state_heap σ1 !! (l +ₗ i) = None) ->
  mirror es1 σ1 κ -∗
  (mirror (<[tid := fill K #l]> es1 ++ [])
            (state_alloc l (Header tag (Z.to_nat n)) (replicate (Z.to_nat n) ()%V) σ1)
            (κ ++ [])
   -∗ goal E) -∗
  goal E.
Proof.
  intros Hlook H0 H1 Hheap_l H2.
  iIntros "Hext Hcont".
  iEval (rewrite mirror_unfold) in "Hext".
  iDestruct "Hext" as "(%φ & %ψ & %Hok & Hes & Hloc & Hheap & Hhdrs & Horphans & Hpm)".
  pose proof (proj1 Hok) as Hinv. pose proof (proj2 Hok) as Hpwf.
  pose proof Hinv as Hinv'.
  destruct Hinv' as [Hnd Hlen Hdomh Hdomhd Hdomψ Hcodomψ Hinj Hwfes Hwfls Hwfhp Hblock Hpart].
  pose proof Hlook as Hlook'.
  apply lookup_lt_Some in Hlook'.
  iDestruct (big_sepL2_length with "Hes") as %Hlen'.
  destruct (lookup_lt_is_Some_2 φ tid) as [pid Hpid]; first lia.
  destruct (lookup_lt_is_Some_2 σ1.(state_locals) tid) as [vloc Hvloc]; first lia.
  rewrite (big_sepL2_delete' _ _ _ tid) //.
  iDestruct "Hes" as "[Hrun Hes]".
  rewrite tr_fill /=.
  iApply (goal_alloc _ _ _ tag n H0 with "Hrun").
  iIntros (l') "Hhdr' Hcells' Horph Hrun".
  (* Derive codomain freshness from cell + orphan tokens. *)
  iAssert (⌜∀ i : nat, (i < Z.to_nat n)%nat → ∀ l0 v, ψ !! l0 = Some v → v ≠ l' +ₗ Z.of_nat i⌝)%I
    with "[Hheap Hcells' Horphans]" as %Hcodom_fresh.
  { iIntros (i Hi l0 v Hψl0 Heq). subst v.
    iDestruct (big_sepL_lookup _ _ i ()%V with "Hcells'") as "[_ Hcell_tok]".
    { apply lookup_replicate. split; [done|lia]. }
    iApply (mirror_loc_tok_excluded with "Hheap Horphans Hcell_tok"); eauto. }
  iAssert (⌜∀ l0 v, ψ !! l0 = Some v → v ≠ l'⌝)%I
    with "[Hheap Hcells' Horphans Horph]" as %Hcodom_fresh0.
  { iIntros (l0 v Hψl0 Heq). subst v.
    destruct (decide (Z.to_nat n = 0%nat)) as [Hzn|Hzn].
    - assert (Hn_zero : n = 0%Z) by lia.
      iSpecialize ("Horph" with "[//]").
      iApply (mirror_loc_tok_excluded with "Hheap Horphans Horph"); eauto.
    - assert (Hzn_pos : (0 < Z.to_nat n)%nat) by lia.
      iPureIntro.
      apply (Hcodom_fresh 0%nat Hzn_pos _ _ Hψl0).
      by rewrite Nat2Z.inj_0 location_add_0. }
  iApply "Hcont". rewrite !app_nil_r.
  (* Repackage with [vs := replicate (Z.to_nat n) ValUnit] for the unified helper. *)
  set (vs := replicate (Z.to_nat n) ()%V).
  assert (Hlen_vs : length vs = Z.to_nat n) by apply length_replicate.
  assert (Hwf_vs : Forall (wf_val ψ) vs).
  { apply Forall_forall. intros v Hv. apply elem_of_replicate in Hv as [-> _].
    rewrite /wf_val /=. set_solver. }
  (* Massage the cells, the orphan-token wand, and the goal to the helper's shape. *)
  iAssert ([∗ list] i ↦ v ∈ vs, (l' +ₗ Z.of_nat i) ↦ tr_val ψ v)%I
    with "[Hcells']" as "Hcells'".
  { iApply (big_sepL_mono with "Hcells'"). intros k v Hk.
    apply lookup_replicate in Hk as [-> _]. done. }
  iAssert (⌜length vs = 0%nat⌝ -∗ loc_tok1 l')%I with "[Horph]" as "Horph".
  { iIntros (Heq). rewrite Hlen_vs in Heq.
    iApply "Horph". iPureIntro. lia. }
  assert (H2' : ∀ i, (i < length vs)%nat →
           state_headers σ1 !! (l +ₗ i) = None ∧
           state_heap σ1 !! (l +ₗ i) = None).
  { intros i Hi. apply H2. by rewrite -Hlen_vs. }
  assert (Hcodom_fresh' : ∀ i, (i < length vs)%nat → ∀ l0 v,
            ψ !! l0 = Some v → v ≠ l' +ₗ Z.of_nat i).
  { intros i Hi. rewrite Hlen_vs in Hi. by apply Hcodom_fresh. }
  rewrite -Hlen_vs.
  iApply (mirror_resources_alloc φ ψ es1 σ1 tid pid K _ vloc tag vs l l' κ
            Hinv Hpwf Hpid Hvloc Hlook Hwf_vs H1 Hheap_l H2' Hcodom_fresh0 Hcodom_fresh'
            with "Hes Hloc Hheap Hhdrs Horphans Hhdr' Hcells' Horph Hpm Hrun").
Qed.

Lemma update_mirror_step_block_mutable (E : coPset) (es1 : list expr) (σ1 : state)
  (κ : list observation)
  (tid : nat) (K : ectx) (tag : nat) (vs : list val) (l : location) :
  es1 !! tid = Some (fill K (Block Mutable tag (of_vals vs))) ->
  0 < length vs ->
  state_headers σ1 !! l = None ->
  state_heap σ1 !! l = None ->
  (∀ i, (i < length vs)%nat →
     state_headers σ1 !! (l +ₗ i) = None ∧
     state_heap σ1 !! (l +ₗ i) = None) ->
  mirror es1 σ1 κ -∗
  (mirror (<[tid := fill K #l]> es1 ++ [])
            (state_alloc l (Header tag (length vs)) vs σ1)
            (κ ++ [])
   -∗ goal E) -∗
  goal E.
Proof.
  intros Hlook Hpos H1 Hheap_l H2.
  iIntros "Hext Hcont".
  iEval (rewrite mirror_unfold) in "Hext".
  iDestruct "Hext" as "(%φ & %ψ & %Hok & Hes & Hloc & Hheap & Hhdrs & Horphans & Hpm)".
  pose proof (proj1 Hok) as Hinv. pose proof (proj2 Hok) as Hpwf.
  pose proof Hinv as Hinv'.
  destruct Hinv' as [Hnd Hlen Hdomh Hdomhd Hdomψ Hcodomψ Hinj Hwfes Hwfls Hwfhp Hblock Hpart].
  pose proof Hlook as Hlook'.
  apply lookup_lt_Some in Hlook'.
  iDestruct (big_sepL2_length with "Hes") as %Hlen'.
  destruct (lookup_lt_is_Some_2 φ tid) as [pid Hpid]; first lia.
  destruct (lookup_lt_is_Some_2 σ1.(state_locals) tid) as [vloc Hvloc]; first lia.
  rewrite (big_sepL2_delete' _ _ _ tid) //.
  iDestruct "Hes" as "[Hrun Hes]".
  rewrite tr_fill /=.
  pose proof (Forall_lookup_1 _ _ _ _ Hwfes Hlook) as Hwf_block.
  apply wf_fill in Hwf_block as [_ Hwf_block].
  rewrite /wf_expr /= in Hwf_block.
  assert (Hwf_vs : Forall (wf_val ψ) vs).
  { apply Forall_forall. intros v Hv.
    rewrite /wf_val. etrans; last exact Hwf_block.
    intros x Hx.
    apply elem_of_union_list. exists (locs_val v). split; last done.
    apply list_elem_of_fmap. eexists (Val v); split; first done.
    rewrite /of_vals. apply list_elem_of_fmap. by exists v. }
  rewrite -tr_of_vals.
  iApply (goal_block_mutable _ _ _ tag (tr_val ψ <$> vs) with "Hrun").
  { rewrite length_fmap. exact Hpos. }
  iIntros (l') "Hhdr' Hcells' Hrun".
  rewrite length_fmap.
  (* Derive codomain freshness from the cell tokens (size > 0). *)
  iAssert (⌜∀ i : nat, (i < length vs)%nat → ∀ l0 v, ψ !! l0 = Some v → v ≠ l' +ₗ Z.of_nat i⌝)%I
    with "[Hheap Hcells' Horphans]" as %Hcodom_fresh.
  { iIntros (i Hi l0 v Hψl0 Heq). subst v.
    destruct (lookup_lt_is_Some_2 vs i Hi) as [vi Hvi].
    iDestruct (big_sepL_lookup _ _ i (tr_val ψ vi) with "Hcells'") as "[_ Hcell_tok]".
    { rewrite list_lookup_fmap Hvi //. }
    iApply (mirror_loc_tok_excluded with "Hheap Horphans Hcell_tok"); eauto. }
  assert (Hcodom_fresh0 : ∀ l0 v, ψ !! l0 = Some v → v ≠ l').
  { intros l0 v Hψl0 ->.
    apply (Hcodom_fresh 0%nat Hpos _ _ Hψl0).
    by rewrite Nat2Z.inj_0 location_add_0. }
  iApply "Hcont". rewrite !app_nil_r.
  (* Reshape Hcells' to canonical "[∗ list] i↦v ∈ vs, ... ↦ tr_val ψ v" form,
     and produce the (vacuous) orphan-token wand. *)
  rewrite big_sepL_fmap.
  iAssert (⌜length vs = 0%nat⌝ -∗ loc_tok1 l')%I as "Horph".
  { iIntros (Heq). exfalso. lia. }
  iApply (mirror_resources_alloc φ ψ es1 σ1 tid pid K _ vloc tag vs l l' κ
            Hinv Hpwf Hpid Hvloc Hlook Hwf_vs H1 Hheap_l H2 Hcodom_fresh0 Hcodom_fresh
            with "Hes Hloc Hheap Hhdrs Horphans Hhdr' Hcells' Horph Hpm Hrun").
Qed.

Lemma update_mirror_step E es1 σ1 κ es2 σ2 κ' :
  step (es1, σ1) κ' (es2, σ2) ->
  mirror es1 σ1 κ -∗
  (mirror es2 σ2 (κ ++ κ') -∗ goal E) -∗
  goal E.
Proof.
  intros (κ0 & tid & e1 & e2 & σ2' & efs & Hpstep & Hlook & Heq & Hwfa1 & ->).
  injection Heq as -> ->.
  inversion Hpstep as [K e1' e2' Heq1 Heq2 Hbstep]; subst e1 e2.
  change ((es1, σ1).2) with σ1 in Hwfa1.
  iIntros "Hext Hcont".
  iEval (rewrite mirror_unfold) in "Hext".
  iDestruct "Hext" as "(%φ & %ψ & %Hok & Hes & Hloc & Hheap & Hhdrs & Horphans & Hpm)".
  pose proof (proj1 Hok) as Hinv. pose proof (proj2 Hok) as Hpwf.
  destruct Hinv as [Hnd Hlen Hdomh Hdomhd Hdomψ Hcodomψ Hinj Hwfes Hwfls Hwfhp Hblock Hpart].
  simpl in Hlook.
  pose proof Hlook as Hlook'.
  apply lookup_lt_Some in Hlook'.
  iDestruct (big_sepL2_length with "Hes") as %Hlen'.
  destruct (lookup_lt_is_Some_2 φ tid) as [pid Hpid]; first lia.
  destruct (lookup_lt_is_Some_2 σ1.(state_locals) tid) as [vloc Hvloc]; first lia.
  iDestruct (big_sepL2_insert_acc _ _ _ tid with "Hes") as "[Hrun Hes]"; [done..|].
  iDestruct (big_sepL2_insert_acc _ _ _ tid with "Hloc") as "[Hl Hloc]"; [done..|].
  rewrite tr_fill /=.
  inversion Hbstep; subst.
  - (* base_step_rec *)
    iApply (goal_pure_step _ _ _ (Rec f x (tr_expr ψ e)) _ _ _ with "Hrun"); first done.
    iIntros "Hrun".
    iApply "Hcont". rewrite mirror_unfold !app_nil_r. iExists φ, ψ.
    iSpecialize ("Hes" $! pid (fill K (Val (ValRec f x e))) with "[Hrun]").
    { rewrite tr_fill /=. iFrame. }
    iSpecialize ("Hloc" $! pid _ with "Hl").
    rewrite (list_insert_id φ); last done.
    rewrite (list_insert_id (state_locals σ1)); last done.
    iFrame "Hes Hloc Hheap Hhdrs Horphans Hpm".
    close_ext_pure. solve_wf_pure.
  - (* base_step_app *)
    iApply (goal_app _ _ _ i ((λ r, (r.1, tr_expr ψ r.2)) <$> recs)
              (rec.1, tr_expr ψ rec.2) (tr_val ψ v) with "Hrun").
    { rewrite list_lookup_fmap H0 //=. }
    iIntros "Hrun".
    iApply "Hcont". rewrite mirror_unfold !app_nil_r. iExists φ, ψ.
    iSpecialize ("Hes" $! pid (fill K (eval_app recs rec.1.2 v rec.2)) with "[Hrun]").
    { rewrite tr_fill /= tr_eval_app. iFrame. }
    iSpecialize ("Hloc" $! pid _ with "Hl").
    rewrite (list_insert_id φ); last done.
    rewrite (list_insert_id (state_locals σ1)); last done.
    iFrame "Hes Hloc Hheap Hhdrs Horphans Hpm".
    close_ext_pure.
    eapply wf_fill_mono;
      [|eapply (Forall_lookup_1 _ _ _ _ Hwfes Hlook)].
    simpl. pose proof (locs_eval_app recs rec.1.2 v rec.2) as Hle.
    apply list_elem_of_lookup_2 in H0.
    assert (locs_expr rec.2 ⊆ ⋃ ((λ r, locs_expr r.2) <$> recs)) as Hr2.
    { intros k Hk. apply elem_of_union_list.
      exists (locs_expr rec.2). split; last done.
      apply list_elem_of_fmap. exists rec. done. }
    set_solver.
  - (* base_step_let *)
    iApply (goal_pure_step _ _ _ (Let x (Val (tr_val ψ v1)) (tr_expr ψ e2)) _ _ _ with "Hrun"); first done.
    iIntros "Hrun".
    iApply "Hcont". rewrite mirror_unfold !app_nil_r. iExists φ, ψ.
    iSpecialize ("Hes" $! pid (fill K (subst' x v1 e2)) with "[Hrun]").
    { rewrite tr_fill tr_subst' /=. iFrame. }
    iSpecialize ("Hloc" $! pid _ with "Hl").
    rewrite (list_insert_id φ); last done.
    rewrite (list_insert_id (state_locals σ1)); last done.
    iFrame "Hes Hloc Hheap Hhdrs Horphans Hpm".
    close_ext_pure.
    eapply wf_fill_mono;
      [|eapply (Forall_lookup_1 _ _ _ _ Hwfes Hlook)].
    simpl. pose proof (locs_subst' x v1 e2). set_solver.
  - (* base_step_unop *)
    pose proof (tr_eval_unop ψ _ _ _ H0) as Htr.
    iApply (goal_pure_step _ _ _ (Unop op (Val (tr_val ψ v))) (Val (tr_val ψ v'))
              _ 1 (pure_unop op (tr_val ψ v) (tr_val ψ v')) Htr with "Hrun").
    iIntros "Hrun".
    iApply "Hcont". rewrite mirror_unfold !app_nil_r. iExists φ, ψ.
    iSpecialize ("Hes" $! pid (fill K (Val v')) with "[Hrun]").
    { rewrite tr_fill /=. iFrame. }
    iSpecialize ("Hloc" $! pid _ with "Hl").
    rewrite (list_insert_id φ); last done.
    rewrite (list_insert_id (state_locals σ1)); last done.
    iFrame "Hes Hloc Hheap Hhdrs Horphans Hpm".
    close_ext_pure.
    eapply wf_fill_mono;
      [|eapply (Forall_lookup_1 _ _ _ _ Hwfes Hlook)].
    simpl. rewrite (locs_eval_unop _ _ _ H0). set_solver.
  - (* base_step_binop *)
    pose proof (tr_eval_binop ψ _ _ _ _ H0) as Htr.
    iApply (goal_pure_step _ _ _ (Binop op (Val (tr_val ψ v1)) (Val (tr_val ψ v2))) (Val (tr_val ψ v'))
              _ 1 (pure_binop op (tr_val ψ v1) (tr_val ψ v2) (tr_val ψ v')) Htr with "Hrun").
    iIntros "Hrun".
    iApply "Hcont". rewrite mirror_unfold !app_nil_r. iExists φ, ψ.
    iSpecialize ("Hes" $! pid (fill K (Val v')) with "[Hrun]").
    { rewrite tr_fill /=. iFrame. }
    iSpecialize ("Hloc" $! pid _ with "Hl").
    rewrite (list_insert_id φ); last done.
    rewrite (list_insert_id (state_locals σ1)); last done.
    iFrame "Hes Hloc Hheap Hhdrs Horphans Hpm".
    close_ext_pure.
    eapply wf_fill_mono;
      [|eapply (Forall_lookup_1 _ _ _ _ Hwfes Hlook)].
    simpl. rewrite (locs_eval_binop _ _ _ _ H0). set_solver.
  - (* base_step_equal_fail *)
    iApply (goal_equal_fail _ _ _ (tr_val ψ v1) (tr_val ψ v2) with "Hrun").
    { apply tr_val_nonsimilar; only 1,4: done.
      all: pose proof (Forall_lookup_1 _ _ _ _ Hwfes Hlook) as Hwf;
           apply wf_fill in Hwf as [_ Hwf];
           rewrite /wf_expr /= in Hwf; set_solver. }
    iIntros "Hrun".
    iApply "Hcont". rewrite mirror_unfold !app_nil_r. iExists φ, ψ.
    iSpecialize ("Hes" $! pid (fill K (Val (ValBool false))) with "[Hrun]").
    { rewrite tr_fill /=. iFrame. }
    iSpecialize ("Hloc" $! pid _ with "Hl").
    rewrite (list_insert_id φ); last done.
    rewrite (list_insert_id (state_locals σ1)); last done.
    iFrame "Hes Hloc Hheap Hhdrs Horphans Hpm".
    close_ext_pure. solve_wf_pure.
  - (* base_step_equal_success *)
    iApply (goal_equal_succ _ _ _ (tr_val ψ v1) (tr_val ψ v2) with "Hrun").
    { by apply tr_val_similar. }
    iIntros "Hrun".
    iApply "Hcont". rewrite mirror_unfold !app_nil_r. iExists φ, ψ.
    iSpecialize ("Hes" $! pid (fill K (Val (ValBool true))) with "[Hrun]").
    { rewrite tr_fill /=. iFrame. }
    iSpecialize ("Hloc" $! pid _ with "Hl").
    rewrite (list_insert_id φ); last done.
    rewrite (list_insert_id (state_locals σ1)); last done.
    iFrame "Hes Hloc Hheap Hhdrs Horphans Hpm".
    close_ext_pure. solve_wf_pure.
  - (* base_step_if *)
    destruct b.
    +   iApply (goal_pure_step _ _ _ (If (Val (ValBool true)) (tr_expr ψ e1) (tr_expr ψ e2)) _ _ _ with "Hrun"); first done.
      iIntros "Hrun".
      iApply "Hcont". rewrite mirror_unfold !app_nil_r. iExists φ, ψ.
      iSpecialize ("Hes" $! pid (fill K e1) with "[Hrun]").
      { rewrite tr_fill /=. iFrame. }
      iSpecialize ("Hloc" $! pid _ with "Hl").
      rewrite (list_insert_id φ); last done.
      rewrite (list_insert_id (state_locals σ1)); last done.
      iFrame "Hes Hloc Hheap Hhdrs Horphans Hpm".
      close_ext_pure. solve_wf_pure.
    +   iApply (goal_pure_step _ _ _ (If (Val (ValBool false)) (tr_expr ψ e1) (tr_expr ψ e2)) _ _ _ with "Hrun"); first done.
      iIntros "Hrun".
      iApply "Hcont". rewrite mirror_unfold !app_nil_r. iExists φ, ψ.
      iSpecialize ("Hes" $! pid (fill K e2) with "[Hrun]").
      { rewrite tr_fill /=. iFrame. }
      iSpecialize ("Hloc" $! pid _ with "Hl").
      rewrite (list_insert_id φ); last done.
      rewrite (list_insert_id (state_locals σ1)); last done.
      iFrame "Hes Hloc Hheap Hhdrs Horphans Hpm".
      close_ext_pure. solve_wf_pure.
  - (* base_step_while *)
    pose proof (pure_while (tr_expr ψ e0) (tr_expr ψ e1)) as Hpw.
    iApply (goal_pure_step _ _ _ _ _ _ _ Hpw I with "Hrun").
    iIntros "Hrun".
    iApply "Hcont". rewrite mirror_unfold !app_nil_r. iExists φ, ψ.
    iSpecialize ("Hes" $! pid (fill K (If e0 (e1 ;; While e0 e1) ())%E) with "[Hrun]").
    { rewrite tr_fill /=. iFrame. }
    iSpecialize ("Hloc" $! pid _ with "Hl").
    rewrite (list_insert_id φ); last done.
    rewrite (list_insert_id (state_locals σ1)); last done.
    iFrame "Hes Hloc Hheap Hhdrs Horphans Hpm".
    close_ext_pure. solve_wf_pure.
  - (* base_step_for *)
    destruct (decide (n2 ≤ n1)%Z) as [Hle|Hle]; simpl.
    + pose proof (pure_for n1 n2 (tr_expr ψ e)) as Hpf.
      rewrite decide_True in Hpf; last done.
      iApply (goal_pure_step _ _ _ _ _ _ _ Hpf I with "Hrun").
      iIntros "Hrun".
      iApply "Hcont". rewrite mirror_unfold !app_nil_r. iExists φ, ψ.
      iSpecialize ("Hes" $! pid (fill K ()%E) with "[Hrun]").
      { rewrite tr_fill /=. iFrame. }
      iSpecialize ("Hloc" $! pid _ with "Hl").
      rewrite (list_insert_id φ); last done.
      rewrite (list_insert_id (state_locals σ1)); last done.
      iFrame "Hes Hloc Hheap Hhdrs Horphans Hpm".
      close_ext_pure. solve_wf_pure.
    + pose proof (pure_for n1 n2 (tr_expr ψ e)) as Hpf.
      rewrite decide_False in Hpf; last done.
      iApply (goal_pure_step _ _ _ _ _ _ _ Hpf I with "Hrun").
      iIntros "Hrun".
      iApply "Hcont". rewrite mirror_unfold !app_nil_r. iExists φ, ψ.
      iSpecialize ("Hes" $! pid (fill K (e #n1 ;; For #(n1 + 1) #n2 e)%E) with "[Hrun]").
      { rewrite tr_fill /=. iFrame. }
      iSpecialize ("Hloc" $! pid _ with "Hl").
      rewrite (list_insert_id φ); last done.
      rewrite (list_insert_id (state_locals σ1)); last done.
      iFrame "Hes Hloc Hheap Hhdrs Horphans Hpm".
      close_ext_pure. solve_wf_pure.
  - (* base_step_alloc — see [update_mirror_step_alloc]. *)
    destruct H1 as (H1 & H1b & H2).
    rewrite -tr_fill /=.
    iSpecialize ("Hes" with "Hrun").
    iSpecialize ("Hloc" $! pid _ with "Hl").
    rewrite (list_insert_id φ); last done.
    rewrite (list_insert_id (state_locals σ1)); last done.
    rewrite (list_insert_id es1); last done.
    iApply (update_mirror_step_alloc E es1 σ1 κ tid K tag n l Hlook H0 H1 H1b H2 with "[-Hcont] Hcont").
    rewrite mirror_unfold. iExists φ, ψ. iSplitR; [by iPureIntro|]. iFrame.
  - (* base_step_block_mutable — see [update_mirror_step_block_mutable]. *)
    rewrite length_of_vals in H0, H2.
    destruct H2 as (H2a & H2b & H2c).
    rewrite -tr_fill /=.
    iSpecialize ("Hes" with "Hrun").
    iSpecialize ("Hloc" $! pid _ with "Hl").
    rewrite (list_insert_id φ); last done.
    rewrite (list_insert_id (state_locals σ1)); last done.
    rewrite (list_insert_id es1); last done.
    rewrite length_of_vals.
    iApply (update_mirror_step_block_mutable E es1 σ1 κ tid K tag vs l Hlook H0 H2a H2b H2c with "[-Hcont] Hcont").
    rewrite mirror_unfold. iExists φ, ψ. iSplitR; [by iPureIntro|]. iFrame.
  - (* base_step_block_immutable_nongenerative *)
    rewrite /= -tr_of_vals.
    iApply (goal_pure_step _ _ _ (Block ImmutableNongenerative tag (of_vals (tr_val ψ <$> vs)))
              (Val (ValBlock Nongenerative tag (tr_val ψ <$> vs)))
              _ 1
              (pure_block_immutable_nongenerative tag _ (tr_val ψ <$> vs))
              (to_of_vals _) with "Hrun").
    iIntros "Hrun".
    iApply "Hcont". rewrite mirror_unfold !app_nil_r. iExists φ, ψ.
    iSpecialize ("Hes" $! pid (fill K (Val (ValBlock Nongenerative tag vs))) with "[Hrun]").
    { rewrite tr_fill /=. iFrame. }
    iSpecialize ("Hloc" $! pid _ with "Hl").
    rewrite (list_insert_id φ); last done.
    rewrite (list_insert_id (state_locals σ1)); last done.
    iFrame "Hes Hloc Hheap Hhdrs Horphans Hpm".
    close_ext_pure.
    eapply wf_fill_mono;
      [|eapply (Forall_lookup_1 _ _ _ _ Hwfes Hlook)].
    simpl. rewrite locs_of_vals. set_solver.
  - (* base_step_block_immutable_generative_weak *)
    rewrite /= -tr_of_vals.
    iApply (goal_pure_step _ _ _ (Block ImmutableGenerativeWeak tag (of_vals (tr_val ψ <$> vs)))
              (Val (ValBlock (Generative None) tag (tr_val ψ <$> vs)))
              _ 1
              (pure_block_immutable_generative tag _ (tr_val ψ <$> vs))
              (to_of_vals _) with "Hrun").
    iIntros "Hrun".
    iApply "Hcont". rewrite mirror_unfold !app_nil_r. iExists φ, ψ.
    iSpecialize ("Hes" $! pid (fill K (Val (ValBlock (Generative None) tag vs))) with "[Hrun]").
    { rewrite tr_fill /=. iFrame. }
    iSpecialize ("Hloc" $! pid _ with "Hl").
    rewrite (list_insert_id φ); last done.
    rewrite (list_insert_id (state_locals σ1)); last done.
    iFrame "Hes Hloc Hheap Hhdrs Horphans Hpm".
    close_ext_pure.
    eapply wf_fill_mono;
      [|eapply (Forall_lookup_1 _ _ _ _ Hwfes Hlook)].
    simpl. rewrite locs_of_vals. set_solver.
  - (* base_step_block_immutable_generative_strong *)
    rewrite /= -tr_of_vals.
    iApply (goal_block_immutable_generative_strong _ _ _ tag (tr_val ψ <$> vs) bid with "Hrun").
    iIntros "Hrun".
    iApply "Hcont". rewrite mirror_unfold !app_nil_r. iExists φ, ψ.
    iSpecialize ("Hes" $! pid (fill K (Val (ValBlock (Generative (Some bid)) tag vs))) with "[Hrun]").
    { rewrite tr_fill /=. iFrame. }
    iSpecialize ("Hloc" $! pid _ with "Hl").
    rewrite (list_insert_id φ); last done.
    rewrite (list_insert_id (state_locals σ1)); last done.
    iFrame "Hes Hloc Hheap Hhdrs Horphans Hpm".
    close_ext_pure.
    eapply wf_fill_mono;
      [|eapply (Forall_lookup_1 _ _ _ _ Hwfes Hlook)].
    simpl. rewrite locs_of_vals. set_solver.
  - (* base_step_match_mutable *)
    iDestruct (big_sepM_lookup_acc _ _ l with "Hhdrs") as "[Hh Hhdrs]"; first eassumption.
    iApply (goal_match_mutable _ _ _ _ _ _ _ _ _ _ (tr_eval_match_loc _ _ _ _ _ _ _ _ H1) with "Hrun Hh").
    iIntros "Hh Hrun".
    iDestruct ("Hhdrs" with "Hh") as "Hhdrs".
    iApply "Hcont". rewrite mirror_unfold !app_nil_r. iExists φ, ψ.
    iSpecialize ("Hes" $! pid (fill K e2') with "[Hrun]").
    { rewrite tr_fill /=. iFrame. }
    iSpecialize ("Hloc" $! pid _ with "Hl").
    rewrite (list_insert_id φ); last done.
    rewrite (list_insert_id (state_locals σ1)); last done.
    iFrame "Hes Hloc Hheap Hhdrs Horphans Hpm".
    close_ext_pure.
    eapply wf_fill_mono;
      [|eapply (Forall_lookup_1 _ _ _ _ Hwfes Hlook)].
    simpl. pose proof (locs_eval_match _ _ _ _ _ _ _ H1) as Hem.
    simpl in Hem. set_solver.
  - (* base_step_match_immutable *)
    iApply (goal_pure_step _ _ _ (Match (Val (ValBlock gen tag (tr_val ψ <$> vs))) x (tr_expr ψ e)
              ((λ br, (br.1, tr_expr ψ br.2)) <$> brs)) (tr_expr ψ e2')
              _ 1
              (pure_match _ _ _ _ _ _ _)
              (tr_eval_match_block _ _ _ _ _ _ _ _ H0) with "Hrun").
    iIntros "Hrun".
    iApply "Hcont". rewrite mirror_unfold !app_nil_r. iExists φ, ψ.
    iSpecialize ("Hes" $! pid (fill K e2') with "[Hrun]").
    { rewrite tr_fill /=. iFrame. }
    iSpecialize ("Hloc" $! pid _ with "Hl").
    rewrite (list_insert_id φ); last done.
    rewrite (list_insert_id (state_locals σ1)); last done.
    iFrame "Hes Hloc Hheap Hhdrs Horphans Hpm".
    close_ext_pure.
    eapply wf_fill_mono;
      [|eapply (Forall_lookup_1 _ _ _ _ Hwfes Hlook)].
    simpl. pose proof (locs_eval_match _ _ _ _ _ _ _ H0) as Hem.
    simpl in Hem. set_solver.
  - (* base_step_get_tag_mutable *)
    iDestruct (big_sepM_lookup_acc _ _ l with "Hhdrs") as "[Hh Hhdrs]"; first eassumption.
    iApply (goal_get_tag_mutable with "Hrun Hh").
    iIntros "Hh Hrun".
    iDestruct ("Hhdrs" with "Hh") as "Hhdrs".
    iApply "Hcont". rewrite mirror_unfold !app_nil_r. iExists φ, ψ.
    iSpecialize ("Hes" $! pid (fill K (Val (ValNat (header_tag hdr)))) with "[Hrun]").
    { rewrite tr_fill /=. iFrame. }
    iSpecialize ("Hloc" $! pid _ with "Hl").
    rewrite (list_insert_id φ); last done.
    rewrite (list_insert_id (state_locals σ1)); last done.
    iFrame "Hes Hloc Hheap Hhdrs Horphans Hpm".
    close_ext_pure. solve_wf_pure.
  - (* base_step_get_tag_immutable *)
    pose proof (pure_get_tag gen tag (tr_val ψ <$> vs)) as Hpe.
    assert (0 < length (tr_val ψ <$> vs)) as Hlt by (rewrite length_fmap; done).
    iApply (goal_pure_step _ _ _ (GetTag (Val (ValBlock gen tag (tr_val ψ <$> vs))))
              (Val (ValNat tag))
              _ 1 Hpe Hlt with "Hrun").
    iIntros "Hrun".
    iApply "Hcont". rewrite mirror_unfold !app_nil_r. iExists φ, ψ.
    iSpecialize ("Hes" $! pid (fill K (Val (ValNat tag))) with "[Hrun]").
    { rewrite tr_fill /=. iFrame. }
    iSpecialize ("Hloc" $! pid _ with "Hl").
    rewrite (list_insert_id φ); last done.
    rewrite (list_insert_id (state_locals σ1)); last done.
    iFrame "Hes Hloc Hheap Hhdrs Horphans Hpm".
    close_ext_pure. solve_wf_pure.
  - (* base_step_get_size_mutable *)
    iDestruct (big_sepM_lookup_acc _ _ l with "Hhdrs") as "[Hh Hhdrs]"; first eassumption.
    iApply (goal_get_size_mutable with "Hrun Hh").
    iIntros "Hh Hrun".
    iDestruct ("Hhdrs" with "Hh") as "Hhdrs".
    iApply "Hcont". rewrite mirror_unfold !app_nil_r. iExists φ, ψ.
    iSpecialize ("Hes" $! pid (fill K (Val (ValNat (header_size hdr)))) with "[Hrun]").
    { rewrite tr_fill /=. iFrame. }
    iSpecialize ("Hloc" $! pid _ with "Hl").
    rewrite (list_insert_id φ); last done.
    rewrite (list_insert_id (state_locals σ1)); last done.
    iFrame "Hes Hloc Hheap Hhdrs Horphans Hpm".
    close_ext_pure. solve_wf_pure.
  - (* base_step_get_size_immutable *)
    pose proof (pure_get_size gen tag (tr_val ψ <$> vs)) as Hpe.
    assert (0 < length (tr_val ψ <$> vs)) as Hlt by (rewrite length_fmap; done).
    iApply (goal_pure_step _ _ _ (GetSize (Val (ValBlock gen tag (tr_val ψ <$> vs))))
              (Val (ValNat (length (tr_val ψ <$> vs))))
              _ 1 Hpe Hlt with "Hrun").
    iIntros "Hrun". rewrite length_fmap.
    iApply "Hcont". rewrite mirror_unfold !app_nil_r. iExists φ, ψ.
    iSpecialize ("Hes" $! pid (fill K (Val (ValNat (length vs)))) with "[Hrun]").
    { rewrite tr_fill /=. iFrame. }
    iSpecialize ("Hloc" $! pid _ with "Hl").
    rewrite (list_insert_id φ); last done.
    rewrite (list_insert_id (state_locals σ1)); last done.
    iFrame "Hes Hloc Hheap Hhdrs Horphans Hpm".
    close_ext_pure. solve_wf_pure.
  - (* base_step_get_field_mutable *)
    pose proof (wf_access_fill _ _ _ Hwfa1 eq_refl eq_refl) as Hwa.
    cbn in Hwa.
    destruct Hwa as ([htag hsz] & Hhdr & Hfld_lo & Hfld_hi). simpl in Hfld_hi.
    iDestruct (big_sepM_lookup_acc _ _ l with "Hhdrs") as "[#Hhdr_l Hhdrs]"; first exact Hhdr.
    iDestruct (heap_block_gather ψ σ1 l htag hsz fld Hblock Hpart Hhdr
                 ltac:(lia) with "Hhdr_l Hheap")
      as (vs0) "([%Hlen0 %Hidx0] & Hblk & Hclose)".
    rewrite H0 /= in Hidx0.
    iApply (goal_get_field _ atm _ _ (tr_loc ψ l) fld _ vs0 (tr_val ψ v)
              ltac:(lia) Hidx0 with "Hrun Hblk").
    iIntros "Hblk Hrun".
    iDestruct ("Hclose" $! v with "[Hblk]") as "Hheap".
    { rewrite list_insert_id //. }
    rewrite (insert_id (state_heap σ1) (l +ₗ fld) v) //.
    iDestruct ("Hhdrs" with "Hhdr_l") as "Hhdrs".
    iApply "Hcont". rewrite mirror_unfold !app_nil_r. iExists φ, ψ.
    iSpecialize ("Hes" $! pid (fill K (Val v)) with "[Hrun]").
    { rewrite tr_fill /=. iFrame. }
    iSpecialize ("Hloc" $! pid _ with "Hl").
    rewrite (list_insert_id φ); last done.
    rewrite (list_insert_id (state_locals σ1)); last done.
    iFrame "Hes Hloc Hheap Hhdrs Horphans Hpm".
    close_ext_pure.
    apply wf_fill. split.
    { pose proof (Forall_lookup_1 _ _ _ _ Hwfes Hlook) as Hwf.
      apply wf_fill in Hwf as [? _]. done. }
    { pose proof (Hwfhp _ _ H0) as Hv. simpl in Hv. rewrite /wf_expr /=. done. }
  - (* base_step_get_field_immutable *)
    pose proof (pure_get_field atm gen tag (tr_val ψ <$> vs) fld (tr_val ψ v)) as Hpe.
    assert ((tr_val ψ <$> vs) !! fld = Some (tr_val ψ v)) as Hlk by (rewrite list_lookup_fmap H0 //).
    iApply (goal_pure_step _ _ _ (GetField atm (Val (ValBlock gen tag (tr_val ψ <$> vs))) (Val (ValNat fld)))
              (Val (tr_val ψ v)) _ 1 Hpe Hlk with "Hrun").
    iIntros "Hrun".
    iApply "Hcont". rewrite mirror_unfold !app_nil_r. iExists φ, ψ.
    iSpecialize ("Hes" $! pid (fill K (Val v)) with "[Hrun]").
    { rewrite tr_fill /=. iFrame. }
    iSpecialize ("Hloc" $! pid _ with "Hl").
    rewrite (list_insert_id φ); last done.
    rewrite (list_insert_id (state_locals σ1)); last done.
    iFrame "Hes Hloc Hheap Hhdrs Horphans Hpm".
    close_ext_pure.
    apply wf_fill. split.
    { pose proof (Forall_lookup_1 _ _ _ _ Hwfes Hlook) as Hwf.
      apply wf_fill in Hwf as [? _]. done. }
    { pose proof (Forall_lookup_1 _ _ _ _ Hwfes Hlook) as Hwf.
      apply wf_fill in Hwf as [_ Hwf]. rewrite /wf_expr /= in Hwf |- *.
      apply elem_of_subseteq. intros k Hk.
      apply Hwf. apply elem_of_union_l.
      apply elem_of_union_list. exists (locs_val v). split; last done.
      apply list_elem_of_fmap. exists v. split; first done.
      eapply list_elem_of_lookup_2; eassumption. }
  - (* base_step_set_field *)
    let Hyp := lazymatch goal with H : is_Some _ |- _ => H end in
    destruct Hyp as [v0 Hv0].
    pose proof (wf_access_fill _ _ _ Hwfa1 eq_refl eq_refl) as Hwa.
    cbn in Hwa.
    destruct Hwa as ([htag hsz] & Hhdr & Hfld_lo & Hfld_hi). simpl in Hfld_hi.
    iDestruct (big_sepM_lookup_acc _ _ l with "Hhdrs") as "[#Hhdr_l Hhdrs]"; first exact Hhdr.
    iDestruct (heap_block_gather ψ σ1 l htag hsz fld Hblock Hpart Hhdr
                 ltac:(lia) with "Hhdr_l Hheap")
      as (vs0) "([%Hlen0 %Hidx0] & Hblk & Hclose)".
    rewrite Hv0 /= in Hidx0.
    iApply (goal_set_field _ atm _ _ (tr_loc ψ l) fld (tr_val ψ v0) (tr_val ψ v) vs0
              ltac:(lia) Hidx0 with "Hrun Hblk").
    iIntros "Hblk Hrun".
    iDestruct ("Hclose" $! v with "Hblk") as "Hheap".
    iApply "Hcont". rewrite mirror_unfold !app_nil_r. iExists φ, ψ.
    iSpecialize ("Hes" $! pid (fill K (Val ValUnit)) with "[Hrun]").
    { rewrite tr_fill /=. iFrame. }
    iSpecialize ("Hloc" $! pid _ with "Hl").
    rewrite (list_insert_id φ); last done.
    rewrite (list_insert_id (state_locals σ1)); last done.
    iDestruct ("Hhdrs" with "Hhdr_l") as "Hhdrs".
    iFrame "Hes Hloc".
    rewrite /= /state_set_location /state_update_heap /=.
    iFrame "Hheap Hhdrs Hpm".
    assert (Hin_dom : l +ₗ fld ∈ dom σ1.(state_heap)) by (apply elem_of_dom; eauto).
    rewrite /orphan_headers /=. rewrite dom_insert_L.
    replace ({[l +ₗ fld]} ∪ dom σ1.(state_heap)) with (dom σ1.(state_heap))
      by set_solver.
    iFrame "Horphans".
    close_ext_heap_store.
    { apply Forall_insert; first done;
      apply wf_fill; split;
        [pose proof (Forall_lookup_1 _ _ _ _ Hwfes Hlook) as Hwf;
          apply wf_fill in Hwf as [? _]; done
        | rewrite /wf_expr /=; set_solver]. }
    { apply map_Forall_insert_2; [|done];
      pose proof (Forall_lookup_1 _ _ _ _ Hwfes Hlook) as Hwf;
      apply wf_fill in Hwf as [_ Hwf];
      rewrite /wf_expr /wf_val /= in Hwf |- *; set_solver. }
  - (* base_step_xchg *)
    pose proof (wf_access_fill _ _ _ Hwfa1 eq_refl eq_refl) as Hwa.
    cbn in Hwa.
    destruct Hwa as ([htag hsz] & Hhdr & Hfld_lo & Hfld_hi). simpl in Hfld_hi.
    iDestruct (big_sepM_lookup_acc _ _ l with "Hhdrs") as "[#Hhdr_l Hhdrs]"; first exact Hhdr.
    iDestruct (heap_block_gather ψ σ1 l htag hsz fld Hblock Hpart Hhdr
                 ltac:(lia) with "Hhdr_l Hheap")
      as (vs0) "([%Hlen0 %Hidx0] & Hblk & Hclose)".
    rewrite H0 /= in Hidx0.
    iApply (goal_xchg _ _ _ (tr_loc ψ l) fld (tr_val ψ w) (tr_val ψ v) vs0
              ltac:(lia) Hidx0 with "Hrun Hblk").
    iIntros "Hblk Hrun".
    iDestruct ("Hclose" $! v with "Hblk") as "Hheap".
    iApply "Hcont". rewrite mirror_unfold !app_nil_r. iExists φ, ψ.
    iSpecialize ("Hes" $! pid (fill K (Val w)) with "[Hrun]").
    { rewrite tr_fill /=. iFrame. }
    iSpecialize ("Hloc" $! pid _ with "Hl").
    rewrite (list_insert_id φ); last done.
    rewrite (list_insert_id (state_locals σ1)); last done.
    iDestruct ("Hhdrs" with "Hhdr_l") as "Hhdrs".
    iFrame "Hes Hloc".
    rewrite /= /state_set_location /state_update_heap /=.
    iFrame "Hheap Hhdrs Hpm".
    assert (Hin_dom : l +ₗ fld ∈ dom σ1.(state_heap)) by (apply elem_of_dom; eauto).
    rewrite /orphan_headers /=. rewrite dom_insert_L.
    replace ({[l +ₗ fld]} ∪ dom σ1.(state_heap)) with (dom σ1.(state_heap))
      by set_solver.
    iFrame "Horphans".
    close_ext_heap_store.
    { apply Forall_insert; first done;
      apply wf_fill; split;
        [pose proof (Forall_lookup_1 _ _ _ _ Hwfes Hlook) as Hwf;
          apply wf_fill in Hwf as [? _]; done
      | rewrite /wf_expr /=; pose proof (Hwfhp _ _ H0) as Hw;
          rewrite /wf_val in Hw; done]. }
    { apply map_Forall_insert_2; [|done];
      pose proof (Forall_lookup_1 _ _ _ _ Hwfes Hlook) as Hwf;
      apply wf_fill in Hwf as [_ Hwf];
      rewrite /wf_expr /wf_val /= in Hwf |- *; set_solver. }
  - (* base_step_cas_fail *)
    pose proof (wf_access_fill _ _ _ Hwfa1 eq_refl eq_refl) as Hwa.
    cbn in Hwa.
    destruct Hwa as ([htag hsz] & Hhdr & Hfld_lo & Hfld_hi). simpl in Hfld_hi.
    iDestruct (big_sepM_lookup_acc _ _ l with "Hhdrs") as "[#Hhdr_l Hhdrs]"; first exact Hhdr.
    iDestruct (heap_block_gather ψ σ1 l htag hsz fld Hblock Hpart Hhdr
                 ltac:(lia) with "Hhdr_l Hheap")
      as (vs0) "([%Hlen0 %Hidx0] & Hblk & Hclose)".
    rewrite H0 /= in Hidx0.
    assert (Hns : tr_val ψ v ≉ tr_val ψ v1).
    { apply tr_val_nonsimilar; only 1,4: done.
      - pose proof (Hwfhp _ _ H0) as Hwf. rewrite /wf_val in Hwf. done.
      - pose proof (Forall_lookup_1 _ _ _ _ Hwfes Hlook) as Hwf.
        apply wf_fill in Hwf as [_ Hwf].
        rewrite /wf_expr /= in Hwf. set_solver. }
    iApply (goal_cas_fail _ _ _ (tr_loc ψ l) fld _ (tr_val ψ v1) (tr_val ψ v2) (tr_val ψ v) vs0
              Hns ltac:(lia) Hidx0 with "Hrun Hblk").
    iIntros "Hblk Hrun".
    iDestruct ("Hclose" $! v with "[Hblk]") as "Hheap".
    { rewrite list_insert_id //. }
    rewrite (insert_id (state_heap σ1) (l +ₗ fld) v) //.
    iDestruct ("Hhdrs" with "Hhdr_l") as "Hhdrs".
    iApply "Hcont". rewrite mirror_unfold !app_nil_r. iExists φ, ψ.
    iSpecialize ("Hes" $! pid (fill K (Val (ValBool false))) with "[Hrun]").
    { rewrite tr_fill /=. iFrame. }
    iSpecialize ("Hloc" $! pid _ with "Hl").
    rewrite (list_insert_id φ); last done.
    rewrite (list_insert_id (state_locals σ1)); last done.
    iFrame "Hes Hloc Hheap Hhdrs Horphans Hpm".
    close_ext_pure. solve_wf_pure.
  - (* base_step_cas_success *)
    pose proof (wf_access_fill _ _ _ Hwfa1 eq_refl eq_refl) as Hwa.
    cbn in Hwa.
    destruct Hwa as ([htag hsz] & Hhdr & Hfld_lo & Hfld_hi). simpl in Hfld_hi.
    iDestruct (big_sepM_lookup_acc _ _ l with "Hhdrs") as "[#Hhdr_l Hhdrs]"; first exact Hhdr.
    iDestruct (heap_block_gather ψ σ1 l htag hsz fld Hblock Hpart Hhdr
                 ltac:(lia) with "Hhdr_l Hheap")
      as (vs0) "([%Hlen0 %Hidx0] & Hblk & Hclose)".
    rewrite H0 /= in Hidx0.
    iApply (goal_cas_succ _ _ _ (tr_loc ψ l) fld (tr_val ψ v1) (tr_val ψ v2) (tr_val ψ v) vs0
              (tr_val_similar _ _ _ H1) ltac:(lia) Hidx0 with "Hrun Hblk").
    iIntros "Hblk Hrun".
    iDestruct ("Hclose" $! v2 with "Hblk") as "Hheap".
    iApply "Hcont". rewrite mirror_unfold !app_nil_r. iExists φ, ψ.
    iSpecialize ("Hes" $! pid (fill K (Val (ValBool true))) with "[Hrun]").
    { rewrite tr_fill /=. iFrame. }
    iSpecialize ("Hloc" $! pid _ with "Hl").
    rewrite (list_insert_id φ); last done.
    rewrite (list_insert_id (state_locals σ1)); last done.
    iDestruct ("Hhdrs" with "Hhdr_l") as "Hhdrs".
    iFrame "Hes Hloc".
    rewrite /= /state_set_location /state_update_heap /=.
    iFrame "Hheap Hhdrs Hpm".
    assert (Hin_dom : l +ₗ fld ∈ dom σ1.(state_heap)) by (apply elem_of_dom; eauto).
    rewrite /orphan_headers /=. rewrite dom_insert_L.
    replace ({[l +ₗ fld]} ∪ dom σ1.(state_heap)) with (dom σ1.(state_heap))
      by set_solver.
    iFrame "Horphans".
    close_ext_heap_store.
    { apply Forall_insert; first done;
      apply wf_fill; split;
        [pose proof (Forall_lookup_1 _ _ _ _ Hwfes Hlook) as Hwf;
          apply wf_fill in Hwf as [? _]; done
        | rewrite /wf_expr /=; set_solver]. }
    { apply map_Forall_insert_2; [|done];
      pose proof (Forall_lookup_1 _ _ _ _ Hwfes Hlook) as Hwf;
      apply wf_fill in Hwf as [_ Hwf];
      rewrite /wf_expr /wf_val /= in Hwf |- *; set_solver. }
  - (* base_step_faa *)
    pose proof (wf_access_fill _ _ _ Hwfa1 eq_refl eq_refl) as Hwa.
    cbn in Hwa.
    destruct Hwa as ([htag hsz] & Hhdr & Hfld_lo & Hfld_hi). simpl in Hfld_hi.
    iDestruct (big_sepM_lookup_acc _ _ l with "Hhdrs") as "[#Hhdr_l Hhdrs]"; first exact Hhdr.
    iDestruct (heap_block_gather ψ σ1 l htag hsz fld Hblock Hpart Hhdr
                 ltac:(lia) with "Hhdr_l Hheap")
      as (vs0) "([%Hlen0 %Hidx0] & Hblk & Hclose)".
    rewrite H0 /= in Hidx0.
    iApply (goal_faa _ _ _ (tr_loc ψ l) fld m n vs0 ltac:(lia) Hidx0 with "Hrun Hblk").
    iIntros "Hblk Hrun".
    iDestruct ("Hclose" $! (ValInt (m + n)) with "[Hblk]") as "Hheap".
    { done. }
    iApply "Hcont". rewrite mirror_unfold !app_nil_r. iExists φ, ψ.
    iSpecialize ("Hes" $! pid (fill K (Val (ValInt m))) with "[Hrun]").
    { rewrite tr_fill /=. iFrame. }
    iSpecialize ("Hloc" $! pid _ with "Hl").
    rewrite (list_insert_id φ); last done.
    rewrite (list_insert_id (state_locals σ1)); last done.
    iDestruct ("Hhdrs" with "Hhdr_l") as "Hhdrs".
    iFrame "Hes Hloc".
    rewrite /= /state_set_location /state_update_heap /=.
    iFrame "Hheap Hhdrs Hpm".
    assert (Hin_dom : l +ₗ fld ∈ dom σ1.(state_heap)) by (apply elem_of_dom; eauto).
    rewrite /orphan_headers /=. rewrite dom_insert_L.
    replace ({[l +ₗ fld]} ∪ dom σ1.(state_heap)) with (dom σ1.(state_heap))
      by set_solver.
    iFrame "Horphans".
    close_ext_heap_store.
    { apply Forall_insert; first done;
      apply wf_fill; split;
        [pose proof (Forall_lookup_1 _ _ _ _ Hwfes Hlook) as Hwf;
          apply wf_fill in Hwf as [? _]; done
        | rewrite /wf_expr /=; set_solver]. }
    { apply map_Forall_insert_2; [|done];
      pose proof (Forall_lookup_1 _ _ _ _ Hwfes Hlook) as Hwf;
      apply wf_fill in Hwf as [_ Hwf];
      rewrite /wf_expr /wf_val /= in Hwf |- *; set_solver. }
  - (* base_step_fork *)
    iApply (goal_fork _ _ _ (tr_expr ψ e) (tr_val ψ v) with "Hrun"); first by apply tr_val_immediate.
    iIntros (p') "Hl' Hrun' Hrun".
    iSpecialize ("Hes" $! pid (fill K (Val ValUnit)) with "[Hrun]").
    { rewrite tr_fill /=. iFrame. }
    iSpecialize ("Hloc" $! pid _ with "Hl").
    rewrite (list_insert_id φ); last done.
    rewrite (list_insert_id (state_locals σ1)); last done.
    iAssert ⌜p' ∉ φ⌝%I as %Hfresh.
    { iIntros (Hin).
      apply list_elem_of_lookup_1 in Hin as [j Hj].
      pose proof (lookup_lt_Some _ _ _ Hj) as Hlt.
      destruct (lookup_lt_is_Some_2 (state_locals σ1) j) as [vj Hvj]; first lia.
      iDestruct (big_sepL2_lookup with "Hloc") as "Hlj"; [exact Hj|exact Hvj|].
      iDestruct (ghost_map_elem_ne with "Hl' Hlj") as %?. done. }
    iApply "Hcont". rewrite mirror_unfold !app_nil_r. iExists (φ ++ [p']), ψ.
    simpl. rewrite /state_add_local /state_update_locals /=.
    iFrame "Hheap Hhdrs Hpm".
    rewrite !big_sepL2_app_same_length; cycle 1.
    { left. lia. }
    { left. rewrite length_insert. done. }
    iFrame "Hes Hloc".
    iSplitR.
    { iPureIntro. split; [|exact Hpwf]. constructor; try done.
      - apply NoDup_app. split_and!; try done.
        + intros x Hx ->%list_elem_of_singleton. done.
        + apply NoDup_singleton.
      - rewrite !length_app length_insert /=. lia.
      - apply Forall_app. split.
        + apply Forall_insert; first done.
          apply wf_fill. split.
          * pose proof (Forall_lookup_1 _ _ _ _ Hwfes Hlook) as Hwf.
            apply wf_fill in Hwf as [? _]. done.
          * rewrite /wf_expr /=. set_solver.
        + apply Forall_singleton.
          pose proof (Forall_lookup_1 _ _ _ _ Hwfes Hlook) as Hwf.
          apply wf_fill in Hwf as [_ Hwf].
          rewrite /wf_expr /= in Hwf. done.
      - apply Forall_app. split; first done.
        apply Forall_singleton. rewrite /wf_val locs_val_immediate; [set_solver|done]. }
    simpl. iFrame.
  - (* base_step_get_local *)
    simpl in H0; rewrite Hvloc in H0; injection H0 as ->.
    iApply (goal_get_local with "Hrun Hl").
    iIntros "Hl Hrun".
    iApply "Hcont". rewrite mirror_unfold !app_nil_r. iExists φ, ψ.
    iSpecialize ("Hes" $! pid (fill K (Val v)) with "[Hrun]").
    { rewrite tr_fill /=. iFrame. }
    iSpecialize ("Hloc" $! pid _ with "Hl").
    rewrite (list_insert_id φ); last done.
    rewrite (list_insert_id (state_locals σ1)); last done.
    iFrame "Hes Hloc Hheap Hhdrs Horphans Hpm".
    close_ext_pure.
    apply wf_fill. split.
    { pose proof (Forall_lookup_1 _ _ _ _ Hwfes Hlook) as Hwf.
      apply wf_fill in Hwf as [? _]. done. }
    { rewrite /wf_expr /=. apply (Forall_lookup_1 _ _ _ _ Hwfls Hvloc). }
  - (* base_step_set_local *)
    iApply (goal_set_local _ _ _ _ (tr_val ψ v) with "Hrun Hl").
    iIntros "Hl Hrun".
    iApply "Hcont". rewrite mirror_unfold !app_nil_r. iExists φ, ψ.
    iSpecialize ("Hes" $! pid (fill K (Val ValUnit)) with "[Hrun]").
    { rewrite tr_fill /=. iFrame. }
    iSpecialize ("Hloc" $! pid v with "Hl").
    rewrite (list_insert_id φ); last done.
    iFrame "Hes Hloc Hheap Hhdrs Horphans Hpm".
    iPureIntro. split; [|exact Hpwf]. constructor; eauto.
    { simpl. rewrite /state_set_local /state_update_locals /=. rewrite !length_insert. done. }
    { apply Forall_insert; first done.
      apply wf_fill. split.
      - pose proof (Forall_lookup_1 _ _ _ _ Hwfes Hlook) as Hwf.
        apply wf_fill in Hwf as [? _]. done.
      - rewrite /wf_expr /=. set_solver. }
    { apply Forall_insert; first done.
      pose proof (Forall_lookup_1 _ _ _ _ Hwfes Hlook) as Hwf.
      apply wf_fill in Hwf as [_ Hwf].
      rewrite /wf_expr /wf_val /= in Hwf |- *. set_solver. }
  - (* base_step_emit: the shadow replays it with [goal_emit], appending the
       renamed observation to the shadow trace. *)
    pose proof (Forall_lookup_1 _ _ _ _ Hwfes Hlook) as Hwfr.
    apply wf_fill in Hwfr as [_ Hwfr]. rewrite /wf_expr /= in Hwfr.
    assert (Hwfv : wf_val ψ v) by (rewrite /wf_val; set_solver).
    iEval (cbn [tr_expr tr_val tr_lit]) in "Hrun".
    iApply (goal_emit E pid (tr_ectx ψ K) (tr_val ψ v) (tr_val ψ <$> κ)
              with "Hrun Hpm").
    iIntros "Hrun Hpm".
    iApply "Hcont". rewrite mirror_unfold.
    iExists φ, ψ.
    rewrite fmap_app /=.
    iSpecialize ("Hes" $! pid (fill K Unit) with "[Hrun]").
    { rewrite tr_fill /=. iFrame. }
    iSpecialize ("Hloc" $! pid _ with "Hl").
    rewrite (list_insert_id φ); last done.
    rewrite (list_insert_id (state_locals σ1)); last done.
    rewrite app_nil_r.
    iFrame "Hes Hloc Hheap Hhdrs Horphans".
    iSplitR "Hpm".
    { iPureIntro. split.
      { constructor; try done; [rewrite length_insert; done|].
        apply Forall_insert; first done.
        eapply wf_fill_mono; [|eapply (Forall_lookup_1 _ _ _ _ Hwfes Hlook)].
        simpl. set_solver. }
      { rewrite /trace_wf. apply Forall_app. split; first exact Hpwf.
        by apply Forall_singleton. } }
    iFrame "Hpm".
Qed.

Lemma update_mirror_steps E es1 σ1 κ0 κ es2 σ2 :
  traced_steps (es1, σ1) κ (es2, σ2) ->
  mirror es1 σ1 κ0 -∗
  (mirror es2 σ2 (κ0 ++ κ) -∗ goal E) -∗
  goal E.
Proof.
  intros Htr.
  remember (es1, σ1) as ρ1 eqn:E1.
  remember (es2, σ2) as ρ3 eqn:E3.
  revert es1 σ1 es2 σ2 κ0 E1 E3.
  induction Htr as [ρ | ρ1 κa ρ2 κs ρ3 Hstep Htr IH];
    intros es1 σ1 es2 σ2 κ0 E1 E3.
  - subst ρ. injection E3 as -> ->.
    iIntros "Hext Hcont". rewrite app_nil_r. by iApply "Hcont".
  - subst ρ1. destruct ρ2 as [esb σb]. subst ρ3.
    iIntros "Hext Hcont".
    iApply (update_mirror_step with "Hext"); [exact Hstep|].
    iIntros "Hext'".
    iApply (IH esb σb es2 σ2 (κ0 ++ κa) eq_refl eq_refl with "Hext'").
    rewrite -app_assoc. iApply "Hcont".
Qed.

End utils.

Lemma orphan_headers_init v :
  orphan_headers (initial_state v) = ∅.
Proof. done. Qed.

Lemma mirror_invs_initial e v0 :
  locs_expr e = ∅ → locs_val v0 = ∅ →
  mirror_invs [0] ∅ [e] (initial_state v0).
Proof.
  intros Hloe Hlov0.
  constructor; simpl.
  { apply NoDup_singleton. }
  { done. }
  { done. }
  { done. }
  { set_solver. }
  { set_solver. }
  { rewrite /tr_inj. intros ???. rewrite lookup_empty. done. }
  { apply Forall_singleton. rewrite /wf_expr Hloe //. }
  { apply Forall_singleton. rewrite /wf_val Hlov0 //. }
  { done. }
  { rewrite /block_aligned. intros ?? Hh. rewrite lookup_empty // in Hh. }
  { rewrite /heap_partition /=. split_and!.
    - intros l hdr Hl. rewrite lookup_empty in Hl. discriminate.
    - intros k Hk. rewrite dom_empty_L in Hk. set_solver.
    - intros l1 h1 l2 h2 i1 i2 Hl1. rewrite lookup_empty in Hl1. discriminate. }
Qed.

Lemma tr_expr_empty e : tr_expr ∅ e = e.
Proof. apply tr_locs_out. set_solver. Qed.

Lemma tr_val_empty v : tr_val ∅ v = v.
Proof. apply (proj2 tr_expr_val_locs_out). set_solver. Qed.

(** Completeness with the *most powerful* remaining assertion: the caller is
    handed [remaining (mirror es σ κ)] — the full [mirror] invariant about
    the reachable configuration — rather than an arbitrary [Q] derived from it.
    Every weaker remaining obligation [Q] follows by [update_remaining] against
    [mirror es σ κ -∗ Q]. *)
Lemma completeness e v0 es σ κ :
  traced_steps ([e], initial_state v0) κ (es,σ) ->
  locs_expr e = ∅ -> locs_val v0 = ∅ ->
  (∀ `{hG:!seqlogGS Σ},
    remaining (mirror es σ κ) ∗ running 0 e ∗ local 0 v0 ∗ trace_model [] -∗
    goal ⊤).
Proof.
  intros Hsteps Hloe Hlov0.
  iIntros (??) "(Hrem&Hrun&Hlocal&Hpm)".
  eapply (update_mirror_steps ⊤ _ _ [] κ) in Hsteps.
  iApply (Hsteps with "[Hrun Hlocal Hpm]").
  { rewrite mirror_unfold.
    iExists [0], ∅. simpl.
    iFrame "Hpm".
    rewrite orphan_headers_init !big_sepM_empty big_sepS_empty !right_id.
    iSplitR.
    { iPureIntro. split; [by apply mirror_invs_initial|].
      rewrite /trace_wf /=. constructor. }
    iSplitL "Hrun".
    { rewrite tr_expr_empty //. }
    { rewrite tr_val_empty //. } }
  { iIntros "Hext".
    iApply (fulfill with "[-]"); last done.
    iApply (update_remaining with "[Hext] Hrem").
    by iIntros. }
Qed.
