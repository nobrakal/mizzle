From iris.proofmode Require Import base proofmode.
From stdpp Require Import hlist.

From mizzle.lang Require Import instances.
From mizzle.lang Require Export semantics.

From mizzle.logic Require Import interp goal stuck goal_proof goal_tactics.

(** [assert], copied from Zoo's [zoo_std/assert.v]. Only the program text is
    reproduced: Zoo's WP specs are replaced by the goal-mode specs in
    the specs below.

    The specs below unfold the definition; the [Opaque] declaration sits at
    the end of the file, sealing it for clients. *)

Definition assert : val :=
  vfun: "v" => if: "v" then () else Fail.

Notation "'assert:' e" := (assert e%E) (at level 99) : expr_scope.

(** Goal-mode specs for [assert] (program text above):
      [assert ≜ vfun: "v" => if: "v" then () else Fail].
    Running it on [true] reduces to [()]; on [false] it reaches [Fail], which
    is stuck, so the goal is fulfilled by [is_stuck']. *)

Section assert.
Context `{seqlogGS Σ}.

Lemma goal_assert p ks :
  focused p ks (assert: true) -∗
  (focused p ks () -∗ goal ⊤) -∗
  goal ⊤.
Proof.
  iIntros "Hp Hcont". rewrite /assert.
  g_call "Hp". g_if_true "Hp".
Qed.

Lemma goal_assert_stuck p ks :
  remaining is_stuck' -∗
  focused p ks (assert: false) -∗
  goal ⊤.
Proof.
  iIntros "Hrem Hp". rewrite /assert.
  g_call "Hp". g_if_false "Hp".
  iApply (fulfill_stuck p with "[Hp] Hrem").
  iApply (focused_stuck_call with "Hp"). done.
Qed.

Lemma goal_assert_at K p ks :
  focused p ks (fill K (assert: true)) -∗
  (focused p ks (fill K ()) -∗ goal ⊤) -∗
  goal ⊤.
Proof. rewrite -!fill_app. iApply goal_assert. Qed.

Lemma goal_assert_stuck_at K p ks :
  remaining is_stuck' -∗
  focused p ks (fill K (assert: false)) -∗
  goal ⊤.
Proof. rewrite -!fill_app. iApply goal_assert_stuck. Qed.

End assert.

Tactic Notation "g_assert" constr(Hp) :=
  iStartProof;
  g_locate Hp
    ltac:(fun e' => lazymatch e' with App (Val assert) _ => idtac end)
    ltac:(fun e => fail 1 "g_assert: no [assert: _] redex in" e);
  let spec := mk_spec_1 Hp in
  with_focused_ks_e Hp ltac:(fun ks _ => iApply (ITrm (goal_assert _ ks) hnil spec));
  iIntros Hp;
  iEval (simpl) in Hp.

Tactic Notation "g_assert_stuck" constr(Hp) :=
  iStartProof;
  g_locate Hp
    ltac:(fun e' => lazymatch e' with App (Val assert) _ => idtac end)
    ltac:(fun e => fail 1 "g_assert_stuck: no [assert: _] redex in" e);
  let spec := constr:(("[$] " ++ Hp)%string) in
  with_focused_ks_e Hp ltac:(fun ks _ => iApply (ITrm (goal_assert_stuck _ ks) hnil spec)).

(** Sealed for clients of this spec, now that the proofs above are done. The
    [g_assert] tactics match on [App (Val assert) _], which does not need the
    body, and sealing keeps [simpl] from unfolding it under them. *)
#[global] Opaque assert.
