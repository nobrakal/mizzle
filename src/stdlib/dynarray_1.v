From iris.proofmode Require Import base proofmode.

From mizzle.lang Require Export semantics.

From mizzle.logic Require Import interp goal goal_proof goal_tactics.
From mizzle.stdlib Require Import array.
From mizzle.lang Require Import options.

(** Dynamic arrays, copied from Zoo's [zoo_std/dynarray_1__code.v]. Mizzle only
    ever allocates one (the domain-local storage seed), so only [create] is
    reproduced. The field notations come from Zoo's
    [zoo_std/dynarray_1__types.v]. See the specs below. *)

Notation "'size'" := (
  in_type "zoo_std.dynarray_1.t" 0
)(in custom mizzle_field
).
Notation "'data'" := (
  in_type "zoo_std.dynarray_1.t" 1
)(in custom mizzle_field
).

Definition dynarray_1٠create : val :=
  vfun: <> =>
    { 0, array٠create () }.

(** Goal-mode spec for [dynarray_1٠create] (the only dynarray
    operation the domain runtime uses: the spawn wrapper allocates an
    empty dynarray as the domain-local storage seed). *)

Section dynarray_1.
Context `{seqlogGS Σ}.

Notation focused p ks e := (running p (fill ks e)).

(** [dynarray_1٠create ()] allocates a fresh empty dynarray
    [{ size = 0; data = array٠create () }]. We hand out its full
    ownership. *)
Lemma focused_dynarray_1_create E p ks :
  focused p ks (App (Val dynarray_1٠create) (Val ValUnit)) -∗
  (∀ (ld la : location),
     ld ↦ₕ□ Header 0 2 -∗
     (ld +ₗ 0%Z) ↦ ValInt 0 -∗
     (ld +ₗ 1%Z) ↦ ValLoc la -∗
     focused p ks (Val (ValLoc ld)) -∗ goal E) -∗
  goal E.
Proof.
  iIntros "Hf Hcont". rewrite /dynarray_1٠create. g_call "Hf".
  g_focus (App (Val array٠create) (Val _)) "Hf".
  iApply (focused_array_create with "Hf").
  iIntros (la) "_ _ Hf". iEval (simpl) in "Hf".
  g_focus (Block Mutable _ _) "Hf".
  iApply (goal_block_mutable _ _ _ _ [ValInt 0; ValLoc la] with "Hf");
    first (simpl; lia).
  iIntros (ld) "Hhdr Hcells Hf". iEval (simpl) in "Hf".
  iDestruct "Hcells" as "(Hsz & Hdata & _)".
  iApply ("Hcont" with "Hhdr Hsz Hdata Hf").
Qed.

End dynarray_1.

(** Sealed for clients, now that the proofs above are done. *)
#[global] Opaque dynarray_1٠create.
