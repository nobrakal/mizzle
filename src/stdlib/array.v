From iris.proofmode Require Import base proofmode.
From stdpp Require Import hlist.

From mizzle.lang Require Import instances.
From mizzle.lang Require Export semantics.

From mizzle.lib Require Import big_sepL.
From mizzle.logic Require Import interp goal goal_proof goal_tactics.
From mizzle.stdlib Require Import assume.
From mizzle.lang Require Import options.

(** Arrays, copied from Zoo's [zoo_std/array__code.v] and restricted to the
    operations Mizzle's benchmarks and the specs below use, plus their
    callees. Only the program text is reproduced; the specs are the goal-mode
    ones in the specs below. *)

Definition array٠unsafe_alloc : val :=
  vfun: "sz" =>
    Alloc 0 "sz".

Definition array٠create : val :=
  vfun: <> =>
    array٠unsafe_alloc 0.

Definition array٠size : val :=
  vfun: "t" =>
    GetSize "t".

Definition array٠unsafe_get : val :=
  vfun: "t" "i" =>
    GetField NotAtomic "t" "i".

Definition array٠get : val :=
  vfun: "t" "i" =>
    assume (0 ≤ "i") ;;
    assume ("i" < array٠size "t") ;;
    array٠unsafe_get "t" "i".

Definition array٠unsafe_set : val :=
  vfun: "t" "i" "v" =>
    SetField NotAtomic "t" "i" "v".

Definition array٠set : val :=
  vfun: "t" "i" "v" =>
    assume (0 ≤ "i") ;;
    assume ("i" < array٠size "t") ;;
    array٠unsafe_set "t" "i" "v".

Definition array٠unsafe_fill_slice : val :=
  vfun: "t" "i" "n" "v" =>
    for: "j" := 0 to "n" begin
      array٠unsafe_set "t" ("i" + "j") "v"
    end.

Definition array٠fill : val :=
  vfun: "t" "v" =>
    array٠unsafe_fill_slice "t" 0 (array٠size "t") "v".

Definition array٠unsafe_make : val :=
  vfun: "sz" "v" =>
    let: "t" := array٠unsafe_alloc "sz" in
    array٠fill "t" "v" ;;
    "t".

Definition array٠make : val :=
  vfun: "sz" "v" =>
    assume (0 ≤ "sz") ;;
    array٠unsafe_make "sz" "v".

Definition array٠unsafe_iteri_slice : val :=
  vfun: "fn" "t" "i" "n" =>
    for: "k" := 0 to "n" begin
      "fn" "k" (array٠unsafe_get "t" ("i" + "k"))
    end.

Definition array٠unsafe_applyi_slice : val :=
  vfun: "fn" "t" "i" "n" =>
    array٠unsafe_iteri_slice
      (fun: "k" "v" => array٠unsafe_set "t" ("i" + "k") ("fn" "k" "v"))
      "t"
      "i"
      "n".

Definition array٠applyi : val :=
  vfun: "fn" "t" =>
    array٠unsafe_applyi_slice "fn" "t" 0 (array٠size "t").

Definition array٠unsafe_initi : val :=
  vfun: "sz" "fn" =>
    let: "t" := array٠unsafe_alloc "sz" in
    array٠applyi (fun: "i" <> => "fn" "i") "t" ;;
    "t".

Definition array٠unsafe_init : val :=
  vfun: "sz" "fn" =>
    array٠unsafe_initi "sz" (fun: "_i" => "fn" ()).

Definition array٠init : val :=
  vfun: "sz" "fn" =>
    assume (0 ≤ "sz") ;;
    array٠unsafe_init "sz" "fn".

(** The array program text above is copied from Zoo. The goal-style
    specifications below unfold it directly with [rewrite /array٠…]; the
    primitives are sealed [#[global] Opaque] only at the end of this file,
    so importers cannot unfold them. The [assume] primitive is handled via
    [goal_assume] (in [stdlib/assume.v]). *)

Section array.
Context `{seqlogGS Σ}.

Notation focused p ks e := (running p (fill ks e)).

(** The fill loop at the heart of [array٠make]: starting at counter
    [done_], with [rem] cells still holding their old contents, run the
    [For] loop to completion, leaving every remaining cell set to [v].
    This is a direct user of the [focused_for_*] step lemmas (induction on
    [rem]). *)
Lemma focused_fill_loop E p ks (l:location) (v:val) (done_:nat) (rem:list val) (sz:nat) dqh :
  (done_ + length rem ≤ sz)%nat →
  l ↦ₕ{dqh} Header 0 sz -∗
  ([∗ list] k ↦ w ∈ rem, (l +ₗ Z.of_nat (done_ + k)) ↦ w) -∗
  focused p ks
    (For (Val (ValInt (Z.of_nat done_)))
         (Val (ValInt (Z.of_nat (done_ + length rem))))
         (Rec BAnon (BNamed "j")
            (App (App (App (Val array٠unsafe_set) (Val (ValLoc l)))
                      (Binop BinopPlus (Val (ValInt 0)) (Var "j")))
                 (Val v)))) -∗
  (l ↦ₕ{dqh} Header 0 sz -∗
   ([∗ list] k ↦ w ∈ rem, (l +ₗ Z.of_nat (done_ + k)) ↦ v) -∗
     focused p ks (Val ValUnit) -∗ goal E) -∗
  goal E.
Proof.
  iInduction rem as [|w rem'] "IH" forall (done_).
  - simpl. iIntros (Hle) "Hhdr _ Hf Hcont".
    rewrite Nat.add_0_r.
    g_for "Hf". iApply ("Hcont" with "Hhdr [] Hf"). done.
  - simpl. iIntros (Hle) "Hhdr Hcells Hf Hcont".
    g_for "Hf".
    iDestruct "Hcells" as "[Hhead Htail]".
    rewrite Nat.add_0_r.
    g_rec "Hf". g_call "Hf". g_binop "Hf".
    rewrite /array٠unsafe_set. g_call3 "Hf".
    g_set_field_cell "Hf" "Hhdr" "Hhead". g_let "Hf".
    replace (Z.of_nat done_ + 1)%Z with (Z.of_nat (S done_)) by lia.
    replace (done_ + S (length rem'))%nat with (S done_ + length rem')%nat by lia.
    iAssert ([∗ list] k↦w0 ∈ rem', (l +ₗ Z.of_nat (S done_ + k)) ↦ w0)%I
      with "[Htail]" as "Htail".
    { iApply (big_sepL_mono with "Htail"). iIntros (k x ?) "Hk".
      replace (done_ + S k)%nat with (S done_ + k)%nat by lia. done. }
    assert (S done_ + length rem' ≤ sz)%nat as Hle' by (simpl in Hle; lia).
    iApply ("IH" $! (S done_) Hle' with "Hhdr Htail Hf").
    iIntros "Hhdr Hcells Hf".
    iApply ("Hcont" with "Hhdr [Hhead Hcells] Hf").
    iSplitL "Hhead".
    { iExact "Hhead". }
    iApply (big_sepL_mono with "Hcells"). iIntros (k x ?) "Hk".
    replace (S done_ + k)%nat with (done_ + S k)%nat by lia. done.
Qed.

(** A generic goal-mode specification for [array٠make].
    [array٠make #n v] allocates a fresh length-[n] array (a tag-[0] block)
    with every cell initialized to [v]. *)
Lemma focused_array_make E p ks (n:Z) (v:val) :
  (0 ≤ n)%Z →
  focused p ks (App (App (Val array٠make) (Val (ValInt n))) (Val v)) -∗
  (∀ l:location,
     l ↦ₕ□ Header 0 (Z.to_nat n) -∗
     ([∗ list] i ↦ w ∈ replicate (Z.to_nat n) v, (l +ₗ Z.of_nat i) ↦ w) -∗
     focused p ks (Val (ValLoc l)) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hn) "Hf Hcont".
  rewrite /array٠make.
  g_call2 "Hf".
  g_binop "Hf".
  rewrite (bool_decide_eq_true_2 (0 ≤ n)%Z Hn).
  g_assume "Hf". g_let "Hf".
  rewrite /array٠unsafe_make /array٠unsafe_alloc.
  g_call "Hf". g_rec "Hf". g_call "Hf". g_call "Hf".
  g_focus (Alloc (Val _) (Val _)) "Hf".
  iApply (goal_alloc _ _ _ 0%nat n with "Hf"); first lia.
  iIntros (l) "Hhdr Hcells Horph Hf". iEval (simpl) in "Hf".
  g_let "Hf".
  rewrite /array٠fill. g_call2 "Hf". rewrite /array٠size. g_call "Hf".
  g_focus (GetSize (Val _)) "Hf".
  iApply (focused_get_size_mutable with "Hf Hhdr").
  iIntros "Hhdr Hf". iEval (simpl) in "Hf".
  rewrite /array٠unsafe_fill_slice. g_call4 "Hf".
  g_focus (For (Val _) (Val _) _) "Hf".
  iEval (rewrite -(length_replicate (Z.to_nat n) ValUnit)) in "Hf".
  assert (0 + length (replicate (Z.to_nat n) ValUnit) ≤ Z.to_nat n)%nat as Hb
    by (rewrite length_replicate; lia).
  iApply (focused_fill_loop _ _ _ l v 0 (replicate (Z.to_nat n) ValUnit) (Z.to_nat n) _ Hb
            with "Hhdr [Hcells] Hf").
  { iApply (big_sepL_mono with "Hcells"). iIntros (k x ?) "Hk".
    rewrite Nat.add_0_l //. }
  iIntros "Hhdr2 Hcells Hf". iEval (simpl) in "Hf".
  g_let "Hf".
  iApply ("Hcont" with "Hhdr2 [Hcells] Hf").
  iDestruct (big_sepL.big_sepL_replicate_1 with "Hcells") as "Hcells".
  iApply big_sepL.big_sepL_replicate_2. iExact "Hcells".
Qed.

(** Drive [array٠get #l #i] past its bounds-checks down to the raw
    [GetField NotAtomic #l #i], and stop there (without performing the load). Useful for
    exhibiting a read access. *)
Lemma focused_array_get_to_get_field E p ks (l:location) (i:Z) (sz:nat) dq :
  (0 ≤ i)%Z → (i < Z.of_nat sz)%Z →
  l ↦ₕ{dq} Header 0 sz -∗
  focused p ks (App (App (Val array٠get) (Val (ValLoc l))) (Val (ValInt i))) -∗
  (l ↦ₕ{dq} Header 0 sz -∗ focused p ks (GetField NotAtomic (Val (ValLoc l)) (Val (ValInt i))) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hi Hisz) "Hhdr Hf Hcont".
  rewrite /array٠get. g_call2 "Hf".
  g_binop "Hf".
  assert (bool_decide (0 ≤ i)%Z = true) as -> by (apply bool_decide_eq_true_2; lia).
  g_assume "Hf". g_let "Hf".
  rewrite /array٠size. g_call "Hf".
  g_focus (GetSize (Val _)) "Hf".
  iApply (focused_get_size_mutable with "Hf Hhdr").
  iIntros "Hhdr Hf". iEval (simpl) in "Hf".
  g_binop "Hf".
  assert (bool_decide (i < sz)%Z = true) as -> by (apply bool_decide_eq_true_2; lia).
  g_assume "Hf". g_let "Hf".
  rewrite /array٠unsafe_get. g_call2 "Hf".
  all: iApply ("Hcont" with "Hhdr Hf").
Qed.

(** Full [array٠get #l #i]: performs the load, returning the cell's value. *)
Lemma focused_array_get E p ks (l:location) (i:Z) (sz:nat) dq w :
  (0 ≤ i)%Z → (i < Z.of_nat sz)%Z →
  l ↦ₕ{dq} Header 0 sz -∗
  (l +ₗ i) ↦ w -∗
  focused p ks (App (App (Val array٠get) (Val (ValLoc l))) (Val (ValInt i))) -∗
  ((l +ₗ i) ↦ w -∗ focused p ks (Val w) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hi Hisz) "Hhdr Hcell Hf Hcont".
  iApply (focused_array_get_to_get_field with "Hhdr Hf"); [lia|lia|].
  iIntros "Hhdr Hf".
  iApply (focused_get_field_cell with "Hf Hhdr Hcell"); first (simpl; lia).
  iIntros "Hhdr Hcell Hf". iApply ("Hcont" with "Hcell Hf").
Qed.

(** Drive [array٠set #l #i #w] past its bounds-checks down to the raw
    [SetField NotAtomic #l #i #w], and stop there (without performing the store). *)
Lemma focused_array_set_to_set_field E p ks (l:location) (i:Z) (w:val) (sz:nat) dq :
  (0 ≤ i)%Z → (i < Z.of_nat sz)%Z →
  l ↦ₕ{dq} Header 0 sz -∗
  focused p ks (App (App (App (Val array٠set) (Val (ValLoc l)))
                         (Val (ValInt i))) (Val w)) -∗
  (l ↦ₕ{dq} Header 0 sz -∗ focused p ks (SetField NotAtomic (Val (ValLoc l)) (Val (ValInt i)) (Val w)) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hi Hisz) "Hhdr Hf Hcont".
  rewrite /array٠set. g_call3 "Hf".
  g_binop "Hf".
  assert (bool_decide (0 ≤ i)%Z = true) as -> by (apply bool_decide_eq_true_2; lia).
  g_assume "Hf". g_let "Hf".
  rewrite /array٠size. g_call "Hf".
  g_focus (GetSize (Val _)) "Hf".
  iApply (focused_get_size_mutable with "Hf Hhdr").
  iIntros "Hhdr Hf". iEval (simpl) in "Hf".
  g_binop "Hf".
  assert (bool_decide (i < sz)%Z = true) as -> by (apply bool_decide_eq_true_2; lia).
  g_assume "Hf". g_let "Hf".
  rewrite /array٠unsafe_set. g_call3 "Hf".
  all: iApply ("Hcont" with "Hhdr Hf").
Qed.

(** Full [array٠set #l #i #w]: performs the store, overwriting the cell. *)
Lemma focused_array_set E p ks (l:location) (i:Z) (w:val) (sz:nat) dq v :
  (0 ≤ i)%Z → (i < Z.of_nat sz)%Z →
  l ↦ₕ{dq} Header 0 sz -∗
  (l +ₗ i) ↦ v -∗
  focused p ks (App (App (App (Val array٠set) (Val (ValLoc l)))
                         (Val (ValInt i))) (Val w)) -∗
  ((l +ₗ i) ↦ w -∗ focused p ks (Val ValUnit) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hi Hisz) "Hhdr Hcell Hf Hcont".
  iApply (focused_array_set_to_set_field with "Hhdr Hf"); [lia|lia|].
  iIntros "Hhdr Hf".
  iApply (focused_set_field_cell with "Hf Hhdr Hcell"); first (simpl; lia).
  iIntros "Hhdr Hcell Hf". iApply ("Hcont" with "Hcell Hf").
Qed.

(** [array٠unsafe_alloc #n] reduces to [Alloc 0 #n], producing a fresh
    length-[n] tag-[0] block with cells left at [ValUnit]. Mirrors
    [goal_alloc]. *)
Lemma focused_array_unsafe_alloc E p ks (n:Z) :
  (0 ≤ n)%Z →
  focused p ks (App (Val array٠unsafe_alloc) (Val (ValInt n))) -∗
  (∀ l:location,
     l ↦ₕ□ Header 0 (Z.to_nat n) -∗
     ([∗ list] i ↦ v ∈ replicate (Z.to_nat n) ValUnit, (l +ₗ Z.of_nat i) ↦ v) -∗
     (⌜n = 0%Z⌝ -∗ loc_tok1 l) -∗
     focused p ks (Val (ValLoc l)) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hn) "Hf Hcont". rewrite /array٠unsafe_alloc. g_call "Hf".
  g_focus (Alloc (Val _) (Val _)) "Hf".
  iApply (goal_alloc _ _ _ 0%nat n with "Hf"); first lia.
  iIntros (l) "Hhdr Hcells Horph Hf". iEval (simpl) in "Hf".
  iApply ("Hcont" with "Hhdr Hcells Horph Hf").
Qed.

(** The loop at the heart of [array٠unsafe_fill_slice]: the same shape as
    [focused_fill_loop] but with an arbitrary base offset [i]; the loop
    variable [j] runs [done_ … done_ + length rem] and each step sets the
    cell [l +ₗ (i + j)] to [v]. *)
Lemma focused_fill_slice_loop E p ks (l:location) (i:Z) (v:val) (done_:nat) (rem:list val) (sz:nat) dqh :
  (0 ≤ i)%Z → (i + Z.of_nat (done_ + length rem) ≤ Z.of_nat sz)%Z →
  l ↦ₕ{dqh} Header 0 sz -∗
  ([∗ list] k ↦ w ∈ rem, (l +ₗ (i + Z.of_nat (done_ + k))) ↦ w) -∗
  focused p ks
    (For (Val (ValInt (Z.of_nat done_)))
         (Val (ValInt (Z.of_nat (done_ + length rem))))
         (Rec BAnon (BNamed "j")
            (App (App (App (Val array٠unsafe_set) (Val (ValLoc l)))
                      (Binop BinopPlus (Val (ValInt i)) (Var "j")))
                 (Val v)))) -∗
  (l ↦ₕ{dqh} Header 0 sz -∗
   ([∗ list] k ↦ w ∈ rem, (l +ₗ (i + Z.of_nat (done_ + k))) ↦ v) -∗
     focused p ks (Val ValUnit) -∗ goal E) -∗
  goal E.
Proof.
  iInduction rem as [|w rem'] "IH" forall (done_).
  - simpl. iIntros (Hi Hle) "Hhdr _ Hf Hcont". rewrite Nat.add_0_r.
    g_for "Hf". iApply ("Hcont" with "Hhdr [] Hf"). done.
  - simpl. iIntros (Hi Hle) "Hhdr Hcells Hf Hcont".
    g_for "Hf". iDestruct "Hcells" as "[Hhead Htail]". rewrite Nat.add_0_r.
    g_rec "Hf". g_call "Hf". g_binop "Hf".
    rewrite /array٠unsafe_set. g_call3 "Hf".
    g_set_field_cell "Hf" "Hhdr" "Hhead". g_let "Hf".
    replace (Z.of_nat done_ + 1)%Z with (Z.of_nat (S done_)) by lia.
    replace (done_ + S (length rem'))%nat with (S done_ + length rem')%nat by lia.
    iAssert ([∗ list] k↦w0 ∈ rem', (l +ₗ (i + Z.of_nat (S done_ + k))) ↦ w0)%I
      with "[Htail]" as "Htail".
    { iApply (big_sepL_mono with "Htail"). iIntros (k x ?) "Hk".
      replace (done_ + S k)%nat with (S done_ + k)%nat by lia. done. }
    assert (i + Z.of_nat (S done_ + length rem') ≤ Z.of_nat sz)%Z as Hle'
      by (simpl in Hle; lia).
    iApply ("IH" $! (S done_) Hi Hle' with "Hhdr Htail Hf").
    iIntros "Hhdr Hcells Hf". iApply ("Hcont" with "Hhdr [Hhead Hcells] Hf").
    iSplitL "Hhead".
    { iExact "Hhead". }
    iApply (big_sepL_mono with "Hcells"). iIntros (k x ?) "Hk".
    replace (S done_ + k)%nat with (done_ + S k)%nat by lia. done.
Qed.

(** [array٠unsafe_fill_slice #l #i #n v] sets cells
    [l +ₗ (i + 0) … l +ₗ (i + n)] to [v]. *)
Lemma focused_array_unsafe_fill_slice E p ks (l:location) (i:Z) (v:val) (ws:list val) (sz:nat) dqh :
  (0 ≤ i)%Z → (i + Z.of_nat (length ws) ≤ Z.of_nat sz)%Z →
  l ↦ₕ{dqh} Header 0 sz -∗
  focused p ks (App (App (App (App (Val array٠unsafe_fill_slice) (Val (ValLoc l)))
                              (Val (ValInt i))) (Val (ValInt (Z.of_nat (length ws))))) (Val v)) -∗
  ([∗ list] k ↦ w ∈ ws, (l +ₗ (i + Z.of_nat k)) ↦ w) -∗
  (l ↦ₕ{dqh} Header 0 sz -∗
   ([∗ list] k ↦ w ∈ ws, (l +ₗ (i + Z.of_nat k)) ↦ v) -∗
     focused p ks (Val ValUnit) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hi Hle) "Hhdr Hf Hcells Hcont". rewrite /array٠unsafe_fill_slice. g_call4 "Hf".
  g_focus (For (Val _) (Val _) _) "Hf".
  assert (i + Z.of_nat (0 + length ws) ≤ Z.of_nat sz)%Z as Hle' by (simpl; lia).
  iApply (focused_fill_slice_loop _ _ _ l i v 0 ws sz _ Hi Hle' with "Hhdr [Hcells] Hf").
  { iApply (big_sepL_mono with "Hcells"). iIntros (k x ?) "Hk". rewrite Nat.add_0_l //. }
  iIntros "Hhdr Hcells Hf". iApply ("Hcont" with "Hhdr [Hcells] Hf").
  iApply (big_sepL_mono with "Hcells"). iIntros (k x ?) "Hk". rewrite Nat.add_0_l //.
Qed.

(** [array٠fill #l v] overwrites every cell of the length-[sz] array with [v]. *)
Lemma focused_array_fill E p ks (l:location) (v:val) (sz:nat) dq (ws:list val) :
  length ws = sz →
  l ↦ₕ{dq} Header 0 sz -∗
  focused p ks (App (App (Val array٠fill) (Val (ValLoc l))) (Val v)) -∗
  ([∗ list] k ↦ w ∈ ws, (l +ₗ Z.of_nat k) ↦ w) -∗
  (l ↦ₕ{dq} Header 0 sz -∗
   ([∗ list] k ↦ w ∈ ws, (l +ₗ Z.of_nat k) ↦ v) -∗
     focused p ks (Val ValUnit) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hlen) "Hhdr Hf Hcells Hcont". subst sz.
  rewrite /array٠fill. g_call2 "Hf". rewrite /array٠size. g_call "Hf".
  g_focus (GetSize (Val _)) "Hf".
  iApply (focused_get_size_mutable with "Hf Hhdr").
  iIntros "Hhdr Hf". iEval (simpl) in "Hf".
  rewrite /array٠unsafe_fill_slice. g_call4 "Hf".
  g_focus (For (Val _) (Val _) _) "Hf".
  assert (0 + length ws ≤ length ws)%nat as Hb by lia.
  iApply (focused_fill_loop _ _ _ l v 0 ws (length ws) _ Hb with "Hhdr [Hcells] Hf").
  { iApply (big_sepL_mono with "Hcells"). iIntros (k x ?) "Hk". rewrite Nat.add_0_l //. }
  iIntros "Hhdr Hcells Hf". iEval (simpl) in "Hf".
  iApply ("Hcont" with "Hhdr [Hcells] Hf").
  iApply (big_sepL_mono with "Hcells"). iIntros (k x ?) "Hk". rewrite Nat.add_0_l //.
Qed.

(** [array٠unsafe_make #n v] allocates a fresh length-[n] array with every
    cell initialized to [v]. *)
Lemma focused_array_unsafe_make E p ks (n:Z) (v:val) :
  (0 ≤ n)%Z →
  focused p ks (App (App (Val array٠unsafe_make) (Val (ValInt n))) (Val v)) -∗
  (∀ l:location,
     l ↦ₕ□ Header 0 (Z.to_nat n) -∗
     ([∗ list] i ↦ w ∈ replicate (Z.to_nat n) v, (l +ₗ Z.of_nat i) ↦ w) -∗
     focused p ks (Val (ValLoc l)) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hn) "Hf Hcont". rewrite /array٠unsafe_make. g_call2 "Hf".
  g_focus (App (Val array٠unsafe_alloc) (Val _)) "Hf".
  iApply (focused_array_unsafe_alloc with "Hf"); first lia.
  iIntros (l) "#Hhdr Hcells _ Hf". iEval (simpl) in "Hf". g_let "Hf".
  g_focus (App (App (Val array٠fill) (Val _)) (Val _)) "Hf".
  iApply (focused_array_fill _ _ _ l v (Z.to_nat n) _ (replicate (Z.to_nat n) ValUnit)
            with "Hhdr Hf Hcells"); first by rewrite length_replicate.
  iIntros "_ Hcells Hf". iEval (simpl) in "Hf". g_seq "Hf".
  iApply ("Hcont" with "Hhdr [Hcells] Hf").
  iDestruct (big_sepL.big_sepL_replicate_1 with "Hcells") as "Hcells".
  iApply big_sepL.big_sepL_replicate_2. iExact "Hcells".
Qed.

(** [array٠create ()] allocates a fresh empty (length-[0]) array. *)
Lemma focused_array_create E p ks :
  focused p ks (App (Val array٠create) (Val ValUnit)) -∗
  (∀ l:location,
     l ↦ₕ□ Header 0 0 -∗
     loc_tok1 l -∗
     focused p ks (Val (ValLoc l)) -∗ goal E) -∗
  goal E.
Proof.
  iIntros "Hf Hcont". rewrite /array٠create. g_call "Hf".
  g_focus (App (Val array٠unsafe_alloc) (Val _)) "Hf".
  iApply (focused_array_unsafe_alloc with "Hf"); first lia.
  iIntros (l) "Hhdr _ Horph Hf". iEval (simpl) in "Hf".
  iApply ("Hcont" with "Hhdr [Horph] Hf"). by iApply "Horph".
Qed.

(** [array٠size #l] reduces to [GetSize #l], returning the header size. *)
Lemma focused_array_size E p ks (l:location) (sz:nat) dq :
  l ↦ₕ{dq} Header 0 sz -∗
  focused p ks (App (Val array٠size) (Val (ValLoc l))) -∗
  (l ↦ₕ{dq} Header 0 sz -∗ focused p ks (Val (ValNat sz)) -∗ goal E) -∗
  goal E.
Proof.
  iIntros "Hhdr Hf Hcont". rewrite /array٠size. g_call "Hf".
  g_focus (GetSize (Val _)) "Hf".
  iApply (focused_get_size_mutable with "Hf Hhdr").
  iIntros "Hhdr Hf". iEval (simpl) in "Hf". iApply ("Hcont" with "Hhdr Hf").
Qed.

(** [array٠unsafe_get #l #i] reduces to [GetField NotAtomic #l #i], returning the cell's
    value. *)
Lemma focused_array_unsafe_get E p ks (l:location) (i:Z) (sz:nat) dqh dq w :
  (0 ≤ i)%Z → (i < Z.of_nat sz)%Z →
  l ↦ₕ{dqh} Header 0 sz -∗
  (l +ₗ i) ↦{dq} w -∗
  focused p ks (App (App (Val array٠unsafe_get) (Val (ValLoc l))) (Val (ValInt i))) -∗
  (l ↦ₕ{dqh} Header 0 sz -∗ (l +ₗ i) ↦{dq} w -∗ focused p ks (Val w) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hi Hisz) "Hhdr Hcell Hf Hcont". rewrite /array٠unsafe_get. g_call2 "Hf".
  iApply (focused_get_field_cell with "Hf Hhdr Hcell"); first (simpl; lia).
  iIntros "Hhdr Hcell Hf". iApply ("Hcont" with "Hhdr Hcell Hf").
Qed.

(** [array٠unsafe_set #l #i w] reduces to [SetField NotAtomic #l #i w], overwriting the
    cell. *)
Lemma focused_array_unsafe_set E p ks (l:location) (i:Z) (w:val) (sz:nat) dqh v :
  (0 ≤ i)%Z → (i < Z.of_nat sz)%Z →
  l ↦ₕ{dqh} Header 0 sz -∗
  (l +ₗ i) ↦ v -∗
  focused p ks (App (App (App (Val array٠unsafe_set) (Val (ValLoc l)))
                         (Val (ValInt i))) (Val w)) -∗
  (l ↦ₕ{dqh} Header 0 sz -∗ (l +ₗ i) ↦ w -∗ focused p ks (Val ValUnit) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hi Hisz) "Hhdr Hcell Hf Hcont". rewrite /array٠unsafe_set. g_call3 "Hf".
  iApply (focused_set_field_cell with "Hf Hhdr Hcell"); first (simpl; lia).
  iIntros "Hhdr Hcell Hf". iApply ("Hcont" with "Hhdr Hcell Hf").
Qed.

(** For [array٠init] the per-iteration body is the [applyi] closure
    [fun: "k" "v" => unsafe_set …], whose body mentions [array٠unsafe_set].
    The [g_*] pure-step tactics run [eval simpl], which would δ-unfold that
    [Transparent] op inside the closure and prevent [g_call] from reducing
    the partial application [FN #j]. Marking the ops [simpl never] keeps them
    folded under [simpl] while leaving [rewrite /array٠…] unfolding intact. *)
#[local] Arguments array٠unsafe_set : simpl never.
#[local] Arguments array٠unsafe_get : simpl never.
#[local] Arguments array٠init : simpl never.
#[local] Arguments array٠unsafe_init : simpl never.
#[local] Arguments array٠unsafe_initi : simpl never.
#[local] Arguments array٠applyi : simpl never.
#[local] Arguments array٠unsafe_applyi_slice : simpl never.
#[local] Arguments array٠unsafe_iteri_slice : simpl never.
#[local] Arguments array٠size : simpl never.

(** ** [array٠init] — distinct fresh ref per cell

    The loop combinator [focused_init_refs_loop] runs the [for] loop at the
    heart of [array٠init]'s [applyi]: each iteration reads the (garbage) cell,
    runs the user thunk to allocate a fresh ref, and stores it. Unlike the
    fill loop, the per-iteration work is abstracted into a [Hstep] hypothesis
    (a Gallina [→], reusable across the induction); [focused_array_init]
    discharges it by stepping the concrete initializer body. The persistent
    header is threaded so [Hstep] can use [g_get_field_cell]/[g_set_field_cell]. *)

Lemma focused_init_refs_loop E p (l:location) (v:val) (body:expr) (sz:nat) :
  (∀ (j:nat) ksj (cont:expr) (old:val),
     (j < sz)%nat →
     l ↦ₕ□ Header 0 sz -∗
     focused p ksj (Seq (App body (Val (ValInt (Z.of_nat j)))) cont) -∗
     (l +ₗ Z.of_nat j) ↦ old -∗
     (∀ c:location,
        (l +ₗ Z.of_nat j) ↦ ValLoc c -∗ (c +ₗ 0%Z) ↦ v -∗
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
      ∃ c:location, (l +ₗ Z.of_nat (done_ + k)) ↦ ValLoc c ∗ (c +ₗ 0%Z) ↦ v) -∗
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
    replace (Z.of_nat done_ + 1)%Z with (Z.of_nat (S done_)) by lia.
    iAssert ([∗ list] k↦old ∈ olds', (l +ₗ Z.of_nat (S done_ + k)) ↦ old)%I
      with "[Htail]" as "Htail".
    { iApply (big_sepL_mono with "Htail"). iIntros (k x ?) "Hk".
      replace (done_ + S k)%nat with (S done_ + k)%nat by lia. done. }
    replace (Z.of_nat (done_ + S (length olds')))
      with (Z.of_nat (S done_ + length olds')) by lia.
    assert (S done_ + length olds' ≤ sz)%nat as Hle' by (simpl in Hle; lia).
    iApply (IH (S done_) ks Hle' with "Hhdr Htail Hf").
    iIntros "Hrest Hf".
    iApply ("Hcont" with "[Hcell0 Hc0 Hrest] Hf").
    simpl. rewrite Nat.add_0_r. iSplitL "Hcell0 Hc0".
    { iExists c0. iFrame. }
    { iApply (big_sepL_mono with "Hrest"). iIntros (k x ?) "Hk".
      replace (done_ + S k)%nat with (S done_ + k)%nat by lia. done. }
Qed.

(** [array٠init #n (fun: <> => ref v)] allocates a fresh length-[n] array of
    distinct fresh ref-cells, each holding [v]. *)
Lemma focused_array_init E p ks (n:Z) (v:val) :
  (0 ≤ n)%Z →
  focused p ks (App (App (Val array٠init) (Val (ValInt n)))
                    (fun: <> => ref v)%E) -∗
  (∀ (l:location),
     l ↦ₕ□ Header 0 (Z.to_nat n) -∗
     ([∗ list] i ↦ _ ∈ replicate (Z.to_nat n) ValUnit,
        ∃ c:location, (l +ₗ Z.of_nat i) ↦ ValLoc c ∗ (c +ₗ 0%Z) ↦ v) -∗
     focused p ks (Val (ValLoc l)) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hn) "Hf Hcont".
  rewrite /array٠init.
  g_rec "Hf". g_call2 "Hf".
  g_binop "Hf".
  rewrite (bool_decide_eq_true_2 (0 ≤ n)%Z Hn).
  g_assume "Hf". g_let "Hf".
  rewrite /array٠unsafe_init. g_call2 "Hf".
  rewrite /array٠unsafe_initi. g_rec "Hf". g_call2 "Hf".
  rewrite /array٠unsafe_alloc. g_call "Hf".
  g_focus (Alloc (Val _) (Val _)) "Hf".
  iApply (goal_alloc _ _ _ 0%nat n with "Hf"); first lia.
  iIntros (l) "#Hhdr Hcells _ Hf". iEval (simpl) in "Hf".
  g_let "Hf".
  rewrite /array٠applyi. g_rec "Hf". g_call2 "Hf".
  rewrite /array٠size. g_call "Hf".
  g_focus (GetSize (Val _)) "Hf".
  iApply (focused_get_size_mutable with "Hf Hhdr").
  iIntros "_ Hf". iEval (simpl) in "Hf".
  rewrite /array٠unsafe_applyi_slice. g_call4 "Hf".
  rewrite /array٠unsafe_iteri_slice. g_rec "Hf". g_call4 "Hf".
  iEval (rewrite -(length_replicate (Z.to_nat n) ValUnit)) in "Hf".
  assert (0 + length (replicate (Z.to_nat n) ValUnit) ≤ Z.to_nat n)%nat as Hb
    by (rewrite length_replicate; lia).
  g_focus (For (Val _) (Val _) _) "Hf".
  iApply (focused_init_refs_loop _ _ _ _ _ (Z.to_nat n) _
            (replicate (Z.to_nat n) ValUnit) 0%nat _ Hb
            with "Hhdr [Hcells] Hf").
  { iApply (big_sepL_mono with "Hcells"). iIntros (k x ?) "Hk". rewrite Nat.add_0_l //. }
  iIntros "Hres Hf". iEval (simpl) in "Hf". g_let "Hf".
  iApply ("Hcont" $! l with "Hhdr [Hres] Hf").
  { iApply (big_sepL_mono with "Hres"). iIntros (k x ?) "Hk". rewrite Nat.add_0_l //. }
  Unshelve.
  clear Hb. iIntros (j ksj kont old Hjsz) "#Hhdrj Hf Hcell Hcont".
  (* body = FN j (unsafe_get l (0+j)); read the cell. The header is
     persistent, so we apply [focused_get_field_cell_at] directly and drop the
     returned (still-persistent) header with [_] — [g_get_field_cell] would try to
     re-introduce it under the existing name [Hhdrj] and fail. *)
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
  (* FN j old = unsafe_set l (0+j) (ref v); allocate the fresh ref, store it. *)
  g_call2 "Hf".
  g_call2 "Hf". g_call "Hf". g_call "Hf".
  g_alloc "Hf" "Hc".
  iEval (rewrite mz_block_unfold) in "Hc".
  iDestruct "Hc" as (tag) "[_ Hc]".
  iEval (simpl) in "Hc". iDestruct "Hc" as "[Hc _]".
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

(** The initialization loop [for i := done_ to sz do a[i] := i]. Marches
    thread [p] past it while retaining ownership of all cells (only their
    integerness is remembered, not their exact contents). *)
Lemma focused_set_loop E p ks (l:location) (sz:nat) (done_:nat) (rem:list val) :
  (done_ + length rem = sz)%nat →
  l ↦ₕ□ Header 0 sz -∗
  ([∗ list] k ↦ w ∈ rem, (l +ₗ Z.of_nat (done_ + k)) ↦ w) -∗
  focused p ks
    (For (Val (ValInt (Z.of_nat done_)))
         (Val (ValInt (Z.of_nat sz)))
         (Rec BAnon (BNamed "i")
            (App (App (App (Val array٠set) (Val (ValLoc l)))
                      (Var "i")) (Var "i")))) -∗
  (([∗ list] k ↦ w ∈ rem, ∃ z:Z, (l +ₗ Z.of_nat (done_ + k)) ↦ ValInt z) -∗
     focused p ks (Val ValUnit) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hsz) "#Hhdr".
  iInduction rem as [|w rem'] "IH" forall (done_ Hsz).
  - simpl in *. iIntros "_ Hf Hcont".
    g_for "Hf". iApply ("Hcont" with "[] Hf"). done.
  - simpl. iIntros "Hcells Hf Hcont".
    simpl in Hsz.
    g_for "Hf".
    iDestruct "Hcells" as "[Hhead Htail]".
    rewrite Nat.add_0_r.
    g_rec "Hf". g_call "Hf".
    g_focus (App (App (App (Val array٠set) (Val _)) (Val _)) (Val _)) "Hf".
    iApply (focused_array_set _ _ _ l (Z.of_nat done_) #done_ sz _ w with "Hhdr Hhead Hf"); [lia|lia|].
    iIntros "Hhead Hf". iEval (simpl) in "Hf". g_let "Hf".
    replace (Z.of_nat done_ + 1)%Z with (Z.of_nat (S done_)) by lia.
    iAssert ([∗ list] k↦w0 ∈ rem', (l +ₗ (S done_ + k)%nat) ↦ w0)%I
      with "[Htail]" as "Htail".
    { iApply (big_sepL_mono with "Htail"). iIntros (k x ?) "Hk".
      replace (done_ + S k)%nat with (S done_ + k)%nat by lia. done. }
    iApply ("IH" $! (S done_) with "[%] Htail Hf"); first lia.
    iIntros "Hcells Hf".
    iApply ("Hcont" with "[Hhead Hcells] Hf").
    iSplitL "Hhead".
    { iExists (Z.of_nat done_). iExact "Hhead". }
    iApply (big_sepL_mono with "Hcells"). iIntros (k x ?) "Hk".
    replace (S done_ + k)%nat with (done_ + S k)%nat by lia. iExact "Hk".
Qed.

(** ** Integer-cell ranges

    [zcells l base count] — cells [base .. base+count) of [l], each
    holding some integer. The workhorse invariant for [focused_loop_*]
    (mizzle.logic.goal_tactics): a loop that only stores integers keeps
    it constant. [[card]] *)
Definition zcells (l : location) (base : Z) (count : nat) : iProp Σ :=
  ([∗ list] k ∈ seq 0 count, ∃ z:Z, (l +ₗ (base + Z.of_nat k)%Z) ↦ ValInt z)%I.

(** The definition as an equation, for the rare proof that needs the raw
    big-op (e.g. to convert a hand-built cell list); [rewrite zcells_eq]
    replaces [rewrite /zcells], which the seal after this section forbids. *)
Lemma zcells_eq l base count :
  zcells l base count =
  ([∗ list] k ∈ seq 0 count, ∃ z:Z, (l +ₗ (base + Z.of_nat k)%Z) ↦ ValInt z)%I.
Proof. reflexivity. Qed.

(** Re-index a position-indexed big-op as one over [seq] values. *)
Lemma big_sepL_index_seq {A} (l : list A) (Φ : nat → iProp Σ) :
  ([∗ list] k ↦ _ ∈ l, Φ k) ⊣⊢ ([∗ list] k ∈ seq 0 (length l), Φ k).
Proof.
  revert Φ; induction l as [|a l IH]; intros Φ; simpl; first done.
  rewrite -fmap_S_seq big_sepL_fmap.
  apply bi.sep_proper; first done.
  apply (IH (fun k => Φ (S k))).
Qed.

(** Freshly-made arrays ([focused_array_make]'s cells) are [zcells]. *)
Lemma zcells_of_cells l (base:Z) (vs : list val) :
  (∀ w, w ∈ vs → ∃ z:Z, w = ValInt z) →
  ([∗ list] k ↦ w ∈ vs, (l +ₗ (base + Z.of_nat k)%Z) ↦ w) -∗
  zcells l base (length vs).
Proof.
  rewrite /zcells.
  iIntros (Hint) "H".
  iInduction vs as [|w vs] "IH" forall (base Hint); simpl; first done.
  iDestruct "H" as "[Hw H]".
  iSplitL "Hw".
  { destruct (Hint w) as [z ->]; [constructor|].
    iExists z. rewrite Z.add_0_r //. }
  rewrite -fmap_S_seq big_sepL_fmap.
  iDestruct ("IH" $! (base + 1)%Z with "[%] [H]") as "H".
  { intros ??. apply Hint. by constructor. }
  { iApply (big_sepL_mono with "H"). iIntros (k ? ?) "Hk".
    replace (base + Z.of_nat (S k))%Z with (base + 1 + Z.of_nat k)%Z by lia.
    done. }
  iApply (big_sepL_mono with "H"). iIntros (? y ?) "Hk".
  replace (base + Z.of_nat (S y))%Z with (base + 1 + Z.of_nat y)%Z by lia.
  done.
Qed.

(** [[card]] *)
Lemma zcells_of_replicate l (n:nat) (z:Z) :
  ([∗ list] k ↦ w ∈ replicate n (ValInt z), (l +ₗ Z.of_nat k) ↦ w) -∗
  zcells l 0 n.
Proof.
  iIntros "H".
  assert (∀ w, w ∈ replicate n (ValInt z) → ∃ z':Z, w = ValInt z') as Hint.
  { intros w Hw%elem_of_replicate. naive_solver. }
  iDestruct (zcells_of_cells l 0 _ Hint with "[H]") as "H".
  { iApply (big_sepL_mono with "H"). iIntros (k ? ?) "Hk".
    replace (0 + Z.of_nat k)%Z with (Z.of_nat k) by lia. done. }
  rewrite length_replicate //.
Qed.

(** Split a [zcells] range at relative position [n1]. Use to peel off a
    prefix (e.g. a single cell that a proof tracks exactly) while keeping
    the remainder as a loop invariant. [[card]] *)
Lemma zcells_split l (base:Z) (count n1 : nat) :
  (n1 <= count)%nat →
  zcells l base count -∗
  zcells l base n1 ∗ zcells l (base + Z.of_nat n1) (count - n1).
Proof.
  iIntros (Hn1) "H".
  rewrite /zcells.
  replace count with (n1 + (count - n1))%nat at 1 by lia.
  rewrite seq_app big_sepL_app.
  iDestruct "H" as "[H1 H2]". iFrame "H1".
  iEval (rewrite (Nat.add_comm 0 n1) -(fmap_add_seq n1 0) big_sepL_fmap) in "H2".
  iApply (big_sepL_mono with "H2"). iIntros (? y ?) "Hk".
  replace (base + Z.of_nat (n1 + y))%Z
    with (base + Z.of_nat n1 + Z.of_nat y)%Z by lia.
  done.
Qed.

(** Access cell [i] of a [zcells] range; the wand restores the range. [[card]] *)
Lemma zcells_acc l (base:Z) (count:nat) (i:Z) :
  (base <= i < base + Z.of_nat count)%Z →
  zcells l base count -∗
  (∃ z:Z, (l +ₗ i) ↦ ValInt z) ∗
  ((∃ z:Z, (l +ₗ i) ↦ ValInt z) -∗ zcells l base count).
Proof.
  iIntros (Hi) "H".
  rewrite /zcells.
  iDestruct (big_sepL_lookup_acc _ _ (Z.to_nat (i - base)) (Z.to_nat (i - base))
    with "H") as "[Hc Hrest]".
  { apply lookup_seq. lia. }
  replace (base + Z.of_nat (Z.to_nat (i - base)))%Z with i by lia.
  iFrame.
Qed.

End array.

(** Sealed for clients: with a literal [count] (e.g. [1505]) the unifier would
    otherwise unfold [zcells] into a [seq 0 1505] big-op on every [iApply] /
    [iFrame], which is where a [Coq: Timeout!] in a loop proof comes from.
    Reason about [zcells] only through the lemmas above. *)
#[global] Opaque zcells.

(** ** One-line access tactics

    Each finds the first fully-applied [array٠get]/[array٠set] on the
    evaluation spine of the running hypothesis [Hp], folds the discovered
    context onto [ks] (so no manual [g_focus] is needed), applies the
    matching [focused_array_*] lemma, discharges the two bounds side
    conditions with [lia], and rebinds the post-state under the same names.

    - [g_array_get Hp Hhdr Hc] — performs the read; [Hc] is the cell
      [(l +ₗ i) ↦ w], returned under the same name.
    - [g_array_set Hp Hhdr Hc] — performs the write; ditto.
    - [g_array_get_to_get_field Hp Hhdr] — parks [Hp] AT the raw [GetField]
      (not performed). The returned header copy is dropped, so use with a
      persistent (□) header.
    - [g_array_set_to_set_field Hp Hhdr] — parks [Hp] AT the raw [SetField]; ditto.

    The parking tactics do not [simpl] the hypothesis afterwards: the
    parked [focused p ks' (GetField/SetField NotAtomic …)] form is what [solve_access]
    expects. *)

(** Bounds side condition [(0 ≤ i)%Z] / [(i < sz)%Z] by [lia], naming the
    goal when it is not provable; a no-op on the iris continuation goal. *)
Ltac g_array_sidecond :=
  lazymatch goal with
  | |- environments.envs_entails _ _ => idtac
  | |- ?G => first [ lia | simpl; lia
                   | fail 1 "array access: bounds side condition not provable by lia:" G ]
  end.

Ltac g_locate_array_get Hp name :=
  g_locate Hp
    ltac:(fun e' => lazymatch e' with
          | App (App (Val array٠get) (Val (ValLoc _))) (Val (ValInt _)) => idtac
          end)
    ltac:(fun e => g_miss name open_constr:(App (App (Val array٠get) (Val (ValLoc _))) (Val (ValInt _)))
                          open_constr:(App (App (Val array٠get) _) _) e).
Ltac g_locate_array_set Hp name :=
  g_locate Hp
    ltac:(fun e' => lazymatch e' with
          | App (App (App (Val array٠set) (Val (ValLoc _))) (Val (ValInt _))) (Val _) => idtac
          end)
    ltac:(fun e => g_miss name open_constr:(App (App (App (Val array٠set) (Val (ValLoc _))) (Val (ValInt _))) (Val _))
                          open_constr:(App (App (App (Val array٠set) _) _) _) e).

Tactic Notation "g_array_get" constr(Hp) constr(Hhdr) constr(Hc) :=
  iStartProof;
  g_locate_array_get Hp "g_array_get";
  let spec := constr:((Hhdr ++ " " ++ Hc ++ " " ++ Hp)%string) in
  with_focused_ks_e Hp ltac:(fun ks _ => iApply (ITrm (focused_array_get _ _ ks _ _ _ _ _) hnil spec));
  [ g_array_sidecond
  | g_array_sidecond
  | let intros := constr:((Hc ++ " " ++ Hp)%string) in
    iIntros intros; iEval (simpl) in Hp ].

Tactic Notation "g_array_set" constr(Hp) constr(Hhdr) constr(Hc) :=
  iStartProof;
  g_locate_array_set Hp "g_array_set";
  let spec := constr:((Hhdr ++ " " ++ Hc ++ " " ++ Hp)%string) in
  with_focused_ks_e Hp ltac:(fun ks _ => iApply (ITrm (focused_array_set _ _ ks _ _ _ _ _ _) hnil spec));
  [ g_array_sidecond
  | g_array_sidecond
  | let intros := constr:((Hc ++ " " ++ Hp)%string) in
    iIntros intros; iEval (simpl) in Hp ].

Tactic Notation "g_array_get_to_get_field" constr(Hp) constr(Hhdr) :=
  iStartProof;
  g_locate_array_get Hp "g_array_get_to_get_field";
  let spec := constr:((Hhdr ++ " " ++ Hp)%string) in
  with_focused_ks_e Hp ltac:(fun ks _ => iApply (ITrm (focused_array_get_to_get_field _ _ ks _ _ _ _) hnil spec));
  [ g_array_sidecond
  | g_array_sidecond
  | let intros := constr:(("_ " ++ Hp)%string) in
    iIntros intros ].

Tactic Notation "g_array_set_to_set_field" constr(Hp) constr(Hhdr) :=
  iStartProof;
  g_locate_array_set Hp "g_array_set_to_set_field";
  let spec := constr:((Hhdr ++ " " ++ Hp)%string) in
  with_focused_ks_e Hp ltac:(fun ks _ => iApply (ITrm (focused_array_set_to_set_field _ _ ks _ _ _ _ _) hnil spec));
  [ g_array_sidecond
  | g_array_sidecond
  | let intros := constr:(("_ " ++ Hp)%string) in
    iIntros intros ].

(** [g_array_make Hp l Hhdr Hc] — performs the allocation [array٠make #n v]
    found on the spine of [Hp]: the fresh location is introduced as [l], its
    □ header as [Hhdr], the [replicate n v] cells as [Hc], and [Hp] is rebound
    at [Val (ValLoc l)] (simplified). The [0 ≤ n] side condition is
    discharged by [lia]. *)
Tactic Notation "g_array_make" constr(Hp) ident(l) constr(Hhdr) constr(Hc) :=
  iStartProof;
  g_locate Hp
    ltac:(fun e' => lazymatch e' with
          | App (App (Val array٠make) (Val (ValInt _))) (Val _) => idtac
          end)
    ltac:(fun e => g_miss "g_array_make" open_constr:(App (App (Val array٠make) (Val (ValInt _))) (Val _))
                          open_constr:(App (App (Val array٠make) _) _) e);
  let spec := constr:(Hp) in
  with_focused_ks_e Hp ltac:(fun ks _ => iApply (ITrm (focused_array_make _ _ ks _ _) hnil spec));
  [ g_array_sidecond
  | let intros := constr:(("#" ++ Hhdr ++ " " ++ Hc ++ " " ++ Hp)%string) in
    iIntros (l) intros; iEval (simpl) in Hp ].

(** Sealed for clients, now that the proofs above are done. *)
#[global] Opaque array٠unsafe_alloc array٠create array٠size array٠unsafe_get array٠get array٠unsafe_set array٠set array٠unsafe_fill_slice array٠fill array٠unsafe_make array٠make array٠unsafe_iteri_slice array٠unsafe_applyi_slice array٠applyi array٠unsafe_initi array٠unsafe_init array٠init.
