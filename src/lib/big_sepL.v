(** The two [big_sepL]/[replicate] lemmas Mizzle uses.

    Copied from Zoo's [zoo/iris/bi/big_op/big_sepL.v], which Mizzle reached
    transitively. The module keeps Zoo's name so the call sites can stay
    written as [big_sepL.big_sepL_replicate_1]. Zoo derives these from its own
    [big_sepL_impl_strong] and closes them with diaframe's [iSteps]; the proof
    below goes through [big_sepL_fmap] instead, so it needs neither. *)

From iris.bi Require Import
  big_op.
From iris.proofmode Require Import
  proofmode.

Section big_sepL.
  Context {PROP : bi}.
  Context {A : Type}.

  Implicit Types x : A.
  Implicit Types Φ : nat → A → PROP.

  (** [replicate n x] is the constant map over [seq i n]; stdpp has the
      lemma in the [fmap]-of-a-[replicate] direction only. *)
  #[local] Lemma fmap_const_seq x n i :
    (λ _ : nat, x) <$> seq i n = replicate n x.
  Proof.
    revert i. induction n as [| n IH]; intros i; first done.
    cbn [seq replicate]. rewrite fmap_cons IH //.
  Qed.

  Lemma big_sepL_replicate Φ n x :
    ([∗ list] k ↦ y ∈ replicate n x, Φ k y) ⊣⊢
    [∗ list] k ∈ seq 0 n, Φ k x.
  Proof.
    rewrite -(fmap_const_seq x n 0) big_sepL_fmap.
    apply big_sepL_proper => k j Hj.
    apply lookup_seq in Hj as [-> _].
    rewrite Nat.add_0_l //.
  Qed.
  Lemma big_sepL_replicate_1 Φ n x :
    ([∗ list] k ↦ y ∈ replicate n x, Φ k y) ⊢
    [∗ list] k ∈ seq 0 n, Φ k x.
  Proof.
    rewrite big_sepL_replicate //.
  Qed.
  Lemma big_sepL_replicate_2 Φ n x :
    ([∗ list] k ∈ seq 0 n, Φ k x) ⊢
    [∗ list] k ↦ y ∈ replicate n x, Φ k y.
  Proof.
    rewrite big_sepL_replicate //.
  Qed.
End big_sepL.
