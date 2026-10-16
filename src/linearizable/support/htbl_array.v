(** * Array-backed bucket operations for the hash tables ******************

    The [cases] hash tables back their buckets with a genuine, arbitrary-size
    array of atomic ref-cells. That array is allocated once by
    [create] and never reshaped — only the per-bucket refs' contents change
    via [Atomic.set] / CAS. This file provides goal-phase specs for the two array
    operations the most-general-client hash-table witnesses need:
    [array.init] (in [create], via [goal_array_init_blk]) and [array.get]
    ([goal_array_get]; the witnesses currently step it with [g_array_get]
    from [mizzle.stdlib.array] instead).

    These are *proven* over the goal-mode array library [mizzle.stdlib.array],
    so the hash-table developments rest on no array-specific axiom. *)

(* [array] must precede the mizzle logic notations, or its [↦] shadows
   mizzle's pointsto. [mizzle.lang.instances] is needed by name for the direct
   [reshape_expr] call below (the [g_*] tactics capture it at definition time,
   but this file uses it verbatim). *)
From mizzle.lang Require Import instances.
From mizzle.logic Require Import prelude.
From mizzle.stdlib Require Import assume array.

Section htbl_array.
Context `{seqlogGS Σ}.

Notation focused p ks e := (running p (fill ks e)).

(** Reopen the array primitives [Local]ly, so the bucket-array init below
    unfolds them directly which [stdlib/array.v] seals. *)
#[local] Transparent
  array٠make array٠unsafe_make array٠unsafe_alloc array٠create
  array٠fill array٠unsafe_fill_slice array٠unsafe_set
  array٠size array٠get array٠set array٠unsafe_get
  array٠init array٠unsafe_init array٠unsafe_initi
  array٠applyi array٠unsafe_applyi_slice array٠unsafe_iteri_slice.

(** Split a per-index bundle [∃ c, Φ i c ∗ Ψ c] into the explicit ref list
    plus the two separate big-seps. *)
Lemma big_sepL_split_locs {PROP:bi} {A} (L:list A)
    (Φ:nat→location→PROP) (Ψ:location→PROP) :
  ([∗ list] i↦_ ∈ L, ∃ c:location, Φ i c ∗ Ψ c) ⊢
  ∃ cells:list location, ⌜length cells = length L⌝ ∧
    ([∗ list] i↦c ∈ cells, Φ i c) ∗ ([∗ list] c ∈ cells, Ψ c).
Proof.
  revert Φ. induction L as [|x L' IH]; iIntros (Φ) "H".
  - iExists []. iSplit; first done. iSplit; done.
  - rewrite big_sepL_cons. iDestruct "H" as "[H0 HL]".
    iDestruct "H0" as (c0) "[Hφ0 Hψ0]".
    iDestruct (IH (λ i, Φ (Nat.succ i)) with "HL") as (cells) "(%Hlen & Helts & Hψs)".
    iExists (c0 :: cells). rewrite !big_sepL_cons.
    iSplit; first (iPureIntro; simpl; lia).
    iFrame "Hφ0 Hψ0 Helts Hψs".
Qed.

(** Header-keeping init loop: like [array.focused_init_refs_loop] but it keeps
    each fresh ref's full block [c ↦∗ [v]] (header + cell) rather than dropping
    the header — goal-mode field ops need the header for [wf_access]. *)
Lemma focused_init_refs_loop_blk E p (l:location) (v:val) (body:expr) (sz:nat) :
  (∀ (j:nat) ksj (cont:expr) (old:val),
     (j < sz)%nat →
     l ↦ₕ□ Header 0 sz -∗
     focused p ksj (Seq (App body (Val (ValInt (Z.of_nat j)))) cont) -∗
     (l +ₗ Z.of_nat j) ↦ old -∗
     (∀ c:location,
        (l +ₗ Z.of_nat j) ↦ ValLoc c -∗ c ↦∗ [v] -∗
        focused p ksj cont -∗ goal E) -∗
     goal E) →
  ∀ (olds:list val) (done_:nat) (ks:list ectxi),
  (done_ + length olds ≤ sz)%nat →
  l ↦ₕ□ Header 0 sz -∗
  ([∗ list] k ↦ old ∈ olds, (l +ₗ Z.of_nat (done_ + k)) ↦ old) -∗
  focused p ks
    (For (Val (ValInt (Z.of_nat done_)))
         (Val (ValInt (Z.of_nat (done_ + length olds)))) body) -∗
  (([∗ list] k ↦ _ ∈ olds,
      ∃ c:location, (l +ₗ Z.of_nat (done_ + k)) ↦ ValLoc c ∗ c ↦∗ [v]) -∗
   focused p ks (Val ValUnit) -∗ goal E) -∗
  goal E.
Proof.
  intros Hstep olds.
  induction olds as [|old0 olds' IH]; intros done_ ks Hle.
  - iIntros "#Hhdr _ Hf Hcont". simpl. rewrite Nat.add_0_r.
    g_for "Hf". iApply ("Hcont" with "[] Hf"). done.
  - iIntros "#Hhdr Hcells Hf Hcont".
    g_for "Hf".
    iDestruct "Hcells" as "[Hhead Htail]". rewrite Nat.add_0_r.
    assert (done_ < sz)%nat as Hjlt by (simpl in Hle; lia).
    iApply (Hstep done_ ks _ old0 Hjlt with "Hhdr Hf Hhead").
    iIntros (c0) "Hcell0 Hc0 Hf".
    replace (Z.of_nat done_ + 1)%Z with (Z.of_nat (Datatypes.S done_)) by lia.
    iAssert ([∗ list] k↦old ∈ olds', (l +ₗ Z.of_nat (Datatypes.S done_ + k)) ↦ old)%I
      with "[Htail]" as "Htail".
    { iApply (big_sepL_mono with "Htail"). iIntros (k x ?) "Hk".
      replace (done_ + Datatypes.S k)%nat with (Datatypes.S done_ + k)%nat by lia. done. }
    replace (Z.of_nat (done_ + Datatypes.S (length olds')))
      with (Z.of_nat (Datatypes.S done_ + length olds')) by lia.
    assert (Datatypes.S done_ + length olds' ≤ sz)%nat as Hle' by (simpl in Hle; lia).
    iApply (IH (Datatypes.S done_) ks Hle' with "Hhdr Htail Hf").
    iIntros "Hrest Hf".
    iApply ("Hcont" with "[Hcell0 Hc0 Hrest] Hf").
    simpl. rewrite Nat.add_0_r. iSplitL "Hcell0 Hc0".
    { iExists c0. iFrame. }
    { iApply (big_sepL_mono with "Hrest"). iIntros (k x ?) "Hk".
      replace (Datatypes.S done_ + k)%nat with (done_ + Datatypes.S k)%nat by lia.
      replace (done_ + Datatypes.S k)%nat with (Datatypes.S (done_+k))%nat by lia. done. }
Qed.

(** Goal-phase bucket-array allocation keeping each bucket's block [c ↦∗ [v]].
    [array.init #n (fun <> => ref v)] allocates the array [arr] of [n] distinct
    fresh ref-cells, each holding [v]: the immutable element slot [(arr +ₗ i)]
    points to the [i]-th ref [c], whose block [c ↦∗ [v]]. [[card]] *)
Lemma goal_array_init_blk E p ks (n : nat) (v : val) :
  (0 < n)%nat →
  running p (fill ks ((array٠init #n (fun: <> => ref v))%E)) -∗
  (∀ (arr : location) (cells : list location),
     ⌜length cells = n⌝ -∗
     arr ↦ₕ□ Header 0 n -∗
     ([∗ list] i ↦ c ∈ cells, (arr +ₗ Z.of_nat i) ↦ ValLoc c) -∗
     ([∗ list] c ∈ cells, c ↦∗ [v]) -∗
     running p (fill ks (Val (ValLoc arr))) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hn) "Hf Hcont".
  rewrite /array٠init.
  g_rec "Hf". g_call2 "Hf".
  g_binop "Hf".
  rewrite (bool_decide_eq_true_2 (0 ≤ Z.of_nat n)%Z) ; last lia.
  g_assume "Hf". g_let "Hf".
  rewrite /array٠unsafe_init. g_call2 "Hf".
  rewrite /array٠unsafe_initi. g_rec "Hf". g_call2 "Hf".
  rewrite /array٠unsafe_alloc. g_call "Hf".
  g_focus (Alloc (Val _) (Val _)) "Hf".
  iApply (goal_alloc _ _ _ 0%nat (Z.of_nat n) with "Hf"); first lia.
  iIntros (l) "#Hhdr Hcells _ Hf". iEval (simpl) in "Hf".
  iEval (rewrite Nat2Z.id) in "Hhdr".
  iEval (rewrite Nat2Z.id) in "Hcells".
  g_let "Hf".
  rewrite /array٠applyi. g_rec "Hf". g_call2 "Hf".
  rewrite /array٠size. g_call "Hf".
  g_focus (GetSize (Val _)) "Hf".
  iApply (focused_get_size_mutable with "Hf Hhdr").
  iIntros "_ Hf". iEval (simpl) in "Hf".
  rewrite /array٠unsafe_applyi_slice. g_call4 "Hf".
  rewrite /array٠unsafe_iteri_slice. g_rec "Hf". g_call4 "Hf".
  iEval (rewrite -[in #n](length_replicate n ValUnit)) in "Hf".
  assert (0 + length (replicate n ValUnit) ≤ n)%nat as Hb
    by (rewrite length_replicate; lia).
  g_focus (For (Val _) (Val _) _) "Hf".
  iApply (focused_init_refs_loop_blk _ _ _ _ _ n _
            (replicate n ValUnit) 0%nat _ Hb
            with "Hhdr [Hcells] Hf").
  { iApply (big_sepL_mono with "Hcells"). iIntros (k x ?) "Hk". rewrite Nat.add_0_l //. }
  iIntros "Hres Hf". iEval (simpl) in "Hf". g_let "Hf".
  iDestruct (big_sepL_split_locs _ (λ i c, (l +ₗ Z.of_nat (0+i)) ↦ ValLoc c)%I
               (λ c, c ↦∗ [v])%I with "Hres") as (cells) "(%Hlen & Helts & Hrefs)".
  rewrite length_replicate in Hlen.
  iApply ("Hcont" $! l cells with "[%] Hhdr [Helts] Hrefs Hf"); first lia.
  { iApply (big_sepL_mono with "Helts"). iIntros (k x ?) "Hk". rewrite Nat.add_0_l //. }
  Unshelve.
  clear Hb. iIntros (j ksj kont old Hjsz) "#Hhdrj Hf Hcell Hcont".
  g_rec "Hf". g_call "Hf".
  g_binop "Hf".
  rewrite /array٠unsafe_get. g_call2 "Hf".
  with_focused_ks_e "Hf" ltac:(fun ks e =>
    reshape_expr e ltac:(fun K e' =>
      first
        [ (iApply (focused_get_field_cell_at _ K _ ks _ _ _ _ _ _ with "Hf Hhdrj Hcell");
           first (simpl; lia);
           iIntros "_ Hcell Hf")
        | fail ])).
  g_call2 "Hf".
  g_call2 "Hf". g_call "Hf". g_call "Hf".
  g_alloc "Hf" "Hc".
  g_binop "Hf".
  rewrite /array٠unsafe_set. g_call3 "Hf".
  with_focused_ks_e "Hf" ltac:(fun ks e =>
    reshape_expr e ltac:(fun K e' =>
      first
        [ (iApply (focused_set_field_cell_at _ K _ ks _ _ _ _ _ _ with "Hf Hhdrj Hcell");
           first (simpl; lia);
           iIntros "_ Hcell Hf")
        | fail ])).
  g_let "Hf".
  iApply ("Hcont" $! _ with "Hcell Hc Hf").
Qed.

(** Goal-phase [array.get #arr #i] returning the [i]-th element ref [#c],
    borrowing and returning its (immutable) element pointsto. *)
Lemma goal_array_get E pp ks (arr c : location) (i : Z) (sz : nat) :
  (0 ≤ i)%Z → (i < Z.of_nat sz)%Z →
  arr ↦ₕ□ Header 0 sz -∗ (arr +ₗ i) ↦ ValLoc c -∗
  running pp (fill ks ((array٠get #arr #i)%E)) -∗
  ((arr +ₗ i) ↦ ValLoc c -∗ running pp (fill ks (Val (ValLoc c))) -∗ goal E) -∗ goal E.
Proof.
  iIntros (??) "Hhdr Hcell Hf Hcont".
  iApply (focused_array_get E pp ks arr i sz with "Hhdr Hcell Hf"); [lia|lia|].
  iIntros "Hcell Hf". iApply ("Hcont" with "Hcell Hf").
Qed.

End htbl_array.
