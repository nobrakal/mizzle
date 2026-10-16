(** List auxiliaries needed by Mizzle's language.

    Copied from Zoo's [zoo/common/list.v], restricted to what the language and
    the logic on top of it use: the [simpl_length] rewrite database, the
    index-passing folds [foldri]/[foldr2] that [semantics.v] and
    [instances.v] are phrased with, and the [Prop]-valued (rather than
    inductive) [Foralli]/[Forall2'], which are the shapes the physical-equality
    and evaluation-context proofs recurse on. *)

From stdpp Require Export
  list.

From mizzle.lang Require Import
  prelude.
From mizzle.lang Require Import
  options.

Create HintDb simpl_length.

#[global] Hint Rewrite
  @length_reverse
  @length_app
  @length_insert
  @length_take
  @length_drop
  @length_fmap
  @length_replicate
  @length_seq
  @length_seqZ
  @length_zip_with
: simpl_length.

Tactic Notation "simpl_length" :=
  autorewrite with simpl_length; try done.
Tactic Notation "simpl_length" "/=" :=
  repeat (progress csimpl in * || simpl_length).
Tactic Notation "simpl_length" "in" ne_hyp_list(Hs) :=
  autorewrite with simpl_length in Hs; try done.
Tactic Notation "simpl_length" "/=" "in" ne_hyp_list(Hs) :=
  repeat (progress csimpl in * || simpl_length in Hs).
Tactic Notation "simpl_length" "in" "*" :=
  autorewrite with simpl_length in *; try done.
Tactic Notation "simpl_length" "/=" "in" "*" :=
  repeat (progress csimpl in * || simpl_length in * ).

Section foldri.
  Implicit Types i : nat.

  Fixpoint foldri' `(f : nat → A → B → B) acc l i :=
    match l with
    | [] =>
        acc
    | x :: l =>
        f i x (foldri' f acc l (S i))
    end.
  #[global] Arguments foldri' _ _ _ _ !_ _ / : assert.
  Definition foldri `(f : nat → A → B → B) acc l :=
    foldri' f acc l 0.

  #[local] Lemma foldri'_app `(f : nat → A → B → B) acc l1 l2 i :
    foldri' f acc (l1 ++ l2) i =
    foldri' f (foldri' f acc l2 (i + (length l1))) l1 i.
  Proof.
    move: i. induction l1 as [| x l1 IH] => i.
    - rewrite right_id //.
    - rewrite /= -Nat.add_succ_comm IH //.
  Qed.
  Lemma foldri_app `(f : nat → A → B → B) acc l1 l2 :
    foldri f acc (l1 ++ l2) =
    foldri f (foldri' f acc l2 (length l1)) l1.
  Proof.
    apply @foldri'_app.
  Qed.

  #[local] Lemma foldri'_fmap `(f : nat → A → B → B) `(g : C → A) acc l i :
    foldri' f acc (g <$> l) i = foldri' (λ i x, f i (g x)) acc l i.
  Proof.
    move: i. induction l as [| x l IH] => i /=; first done.
    rewrite IH //.
  Qed.
  Lemma foldri_fmap `(f : nat → A → B → B) `(g : C → A) acc l :
    foldri f acc (g <$> l) = foldri (λ i x, f i (g x)) acc l.
  Proof.
    apply foldri'_fmap.
  Qed.

  #[local] Lemma foldri'_comm `(f : nat → A → B → B) `(g : B → C) h acc l i :
    ( ∀ i x acc,
      h i x (g acc) = g (f i x acc)
    ) →
    foldri' h (g acc) l i = g (foldri' f acc l i).
  Proof.
    intros Hh.
    move: i. induction l as [| x l IH] => i /=; first done.
    rewrite IH //.
  Qed.
  Lemma foldri_comm `(f : nat → A → B → B) `(g : B → C) h acc l :
    ( ∀ i x acc,
      h i x (g acc) = g (f i x acc)
    ) →
    foldri h (g acc) l = g (foldri f acc l).
  Proof.
    apply foldri'_comm.
  Qed.
End foldri.

Section foldr2.
  Context {A1 A2 B : Type}.

  Fixpoint foldr2 (f : A1 → A2 → B → B) acc l1 l2 :=
    match l1 with
    | [] =>
        acc
    | x1 :: l1 =>
        match l2 with
        | [] =>
            acc
        | x2 :: l2 =>
            f x1 x2 (foldr2 f acc l1 l2)
        end
    end.
  #[global] Arguments foldr2 _ _ !_ !_ / : assert.

  Lemma foldr2_app f acc l11 l12 l21 l22 :
    length l11 = length l21 →
      foldr2 f acc (l11 ++ l12) (l21 ++ l22) =
      foldr2 f (foldr2 f acc l12 l22) l11 l21.
  Proof.
    move: l21. induction l11 as [| x1 l11 IH] => l21 Hlength.
    - destruct l21; done.
    - destruct l21; first done.
      simpl. f_equal. naive_solver.
  Qed.
End foldr2.

Section Foralli.
  Context `(P : nat → A → Prop).

  #[local] Fixpoint Foralli' l i :=
    match l with
    | [] =>
        True
    | x :: l =>
        P i x ∧ Foralli' l (S i)
    end.
  #[global] Arguments Foralli' !_ _ / : assert.
  Definition Foralli l :=
    Foralli' l 0.

  #[local] Lemma Foralli'_lookup_1 l i j x :
    Foralli' l i →
    l !! j = Some x →
    P (i + j) x.
  Proof.
    move: l i. induction j => l i.
    all: destruct l; first done.
    - rewrite right_id. naive_solver.
    - rewrite -Nat.add_succ_comm. naive_solver.
  Qed.
  Lemma Foralli_lookup_1 {l} i x :
    Foralli l →
    l !! i = Some x →
    P i x.
  Proof.
    apply Foralli'_lookup_1.
  Qed.

End Foralli.

Section Forall2'.
  Context `(P : A1 → A2 → Prop).

  Fixpoint Forall2' l1 l2 :=
    match l1, l2 with
    | [], [] =>
        True
    | x1 :: l1, x2 :: l2 =>
        P x1 x2 ∧ Forall2' l1 l2
    | _, _ =>
        False
    end.
  #[global] Arguments Forall2' !_ !_ / : assert.

  Lemma Forall2'_Forall2 l1 l2 :
    Forall2' l1 l2 ↔ Forall2 P l1 l2.
  Proof.
    move: l2. induction l1 => l2.
    all: destruct l2; try done.
    all: split; try naive_solver.
    - intros ?%Forall2_nil_cons_inv. done.
    - intros ?%Forall2_cons_nil_inv. done.
    - rewrite Forall2_cons. naive_solver.
  Qed.

  #[global] Instance Forall2'_dec `{!RelDecision P} :
    RelDecision Forall2'.
  Proof.
    refine (
      fix go l1 l2 : Decision (Forall2' l1 l2) :=
        match l1, l2 with
        | [], [] =>
            left _
        | x1 :: l1, x2 :: l2 =>
            cast_if_and
              (decide (P x1 x2))
              (go l1 l2)
        | _, _ =>
            right _
        end
    ).
    all: clear go.
    all: abstract first [constructor; done | inv 1; done].
  Defined.

  Lemma Forall2'_length l1 l2 :
    Forall2' l1 l2 →
    length l1 = length l2.
  Proof.
    rewrite Forall2'_Forall2. apply Forall2_length.
  Qed.
End Forall2'.

Section Forall2'.
  Context `(P : A → A → Prop).

  Lemma Forall2'_refl :
    (∀ x, P x x) →
    Reflexive (Forall2' P).
  Proof.
    intros ? l. induction l; done.
  Defined.
  #[global] Instance Forall2'_reflexive `{!Reflexive P} :
    Reflexive (Forall2' P).
  Proof.
    apply Forall2'_refl. done.
  Qed.

  Lemma Forall2'_sym :
    (∀ x1 x2, P x1 x2 → P x2 x1) →
    Symmetric (Forall2' P).
  Proof.
    intros ? l1. induction l1 => l2.
    all: destruct l2; naive_solver.
  Defined.
  #[global] Instance Forall2'_symmetric `{!Symmetric P} :
    Symmetric (Forall2' P).
  Proof.
    apply Forall2'_sym. done.
  Qed.

  Lemma Forall2'_trans :
    (∀ x1 x2 x3, P x1 x2 → P x2 x3 → P x1 x3) →
    Transitive (Forall2' P).
  Proof.
    intros ? l1. induction l1 => l2 l3.
    all: destruct l2, l3; naive_solver.
  Defined.
  #[global] Instance Forall2'_transitive `{!Transitive P} :
    Transitive (Forall2' P).
  Proof.
    apply Forall2'_trans. done.
  Defined.
End Forall2'.
