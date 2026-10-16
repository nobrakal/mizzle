From iris.proofmode Require Import base proofmode.

From mizzle.lang Require Export semantics.

From mizzle.logic Require Import interp goal goal_proof goal_tactics.
From mizzle.stdlib Require Import ivar_2 dynarray_1.
From mizzle.lang Require Import options.

(** Domains, copied from Zoo's [zoo_std/domain__code.v] — the two definitions Mizzle
    uses, without any of that file's ghost state or WP proofs. See
    the specs below for the goal-mode specs. *)

Definition domain٠spawn : val :=
  vfun: "fn" =>
    let: "t" := ivar_2٠create () in
    Fork (
      let: "local" := dynarray_1٠create () in
      SetLocal "local" ;;
      ivar_2٠set "t" ("fn" ())
    ) ;;
    "t".

Definition domain٠join : val :=
  ivar_2٠get.

(** Goal-mode specs for [domain٠spawn] / [domain٠join] (program text
    above), proved against the real implementation (an ivar set by the
    spawned process and read by the joiner). The code is sealed
    [#[global] Opaque] only at the end of this file. *)

Section domain.
Context `{seqlogGS Σ}.

(** The spawned domain does not run [fn ()] bare: it runs it as the
    argument of [ivar_2٠set t], i.e. under the evaluation context
    [domain_ctx t]. The context is exposed in the specs so that, at join
    time, the wrapper can be symbolically executed. *)
Local Definition domain_ctx (t : val) : list ectxi :=
  [CtxApp2 (App (Val ivar_2٠set) (Val t))].

(** [domain_handle t q ks'] describes the handle value [t] returned by
    [domain٠spawn] (the ivar block, still unset) and ties it to the wrapper
    context [ks'] under which the domain runs [fn ()]. The process index
    [q] of the spawned domain is not constrained by the definition; it only
    keeps the spawn and join specs indexed by the same process. *)
Definition domain_handle (t : val) (q : nat) (ks' : list ectxi) : iProp Σ :=
  ∃ (l lm : location),
    ⌜t = ValLoc l⌝ ∗
    ⌜ks' = domain_ctx t⌝ ∗
    l ↦ₕ□ Header 0 3 ∗
    (l +ₗ 0%Z) ↦ ValLoc lm ∗
    (l +ₗ 1%Z) ↦ ValUnit ∗
    (l +ₗ 2%Z) ↦ ValUnit ∗
    lm ↦∗ [ValBool false].

(** [domain٠spawn fn] hands the continuation a fresh handle, the spawned
    process [q] focused on [fn ()] (under the wrapper context), and the
    parent back at the handle value. *)
Lemma goal_domain_spawn E p ks (fn : val) :
  focused p ks (App (Val domain٠spawn) (Val fn)) -∗
  (∀ t q ks',
     domain_handle t q ks' -∗
     focused q ks' (App (Val fn) (Val ValUnit)) -∗
     focused p ks (Val t) -∗
     goal E) -∗
  goal E.
Proof.
  iIntros "Hp Hcont". rewrite /domain٠spawn. g_call "Hp".
  (* create the ivar *)
  g_focus (App (Val ivar_2٠create) (Val _)) "Hp".
  iApply (focused_ivar_2_create with "Hp").
  iIntros (l lm) "Hhdr Hmtx Hcond Hres Hlm Hp". iEval (simpl) in "Hp".
  g_let "Hp".
  (* fork the domain *)
  g_fork "Hp" "Hq" "Hloc".
  g_let "Hp".
  (* the spawned process sets up its domain-local storage … *)
  g_focus (App (Val dynarray_1٠create) (Val _)) "Hq".
  iApply (focused_dynarray_1_create with "Hq").
  iIntros (ld la) "_ _ _ Hq". iEval (simpl) in "Hq".
  g_let "Hq".
  iApply (focused_set_local _ _ [CtxLet BAnon _] with "Hq Hloc").
  iIntros "Hloc Hq". iEval (simpl) in "Hq".
  g_let "Hq".
  (* … and is now focused on [fn ()] under the [ivar_2٠set] wrapper *)
  iApply ("Hcont" $! (ValLoc l) _ (domain_ctx (ValLoc l))
            with "[Hhdr Hmtx Hcond Hres Hlm] [Hq] Hp").
  { iExists l, lm. by iFrame. }
  rewrite /domain_ctx /=. iExact "Hq".
Qed.

(** [domain٠join t], once the spawned process has reduced to a value [v]:
    drive the spawned process through the [ivar_2٠set] wrapper (setting
    the result and terminating it), then read the ivar back in the
    joiner. *)
Lemma goal_domain_join E p ks (t : val) q ks' (v : val) :
  focused p ks (App (Val domain٠join) (Val t)) -∗
  domain_handle t q ks' -∗
  focused q ks' (Val v) -∗
  (focused p ks (Val v) -∗ goal E) -∗
  goal E.
Proof.
  iIntros "Hp Hh Hq Hcont".
  iDestruct "Hh" as (l lm) "(-> & -> & Hhdr & Hmtx & Hcond & Hres & Hlm)".
  rewrite {1}/domain_ctx. iEval (simpl) in "Hq".
  (* the spawned process runs the wrapper [ivar_2٠set #l v] to completion *)
  iApply (focused_ivar_2_set _ _ [] with "Hhdr Hmtx Hcond Hres Hlm Hq").
  iIntros "Hhdr Hmtx Hcond Hres Hlm Hq".
  (* the joiner reads the ivar on the fast path *)
  rewrite /domain٠join.
  iApply (focused_ivar_2_get with "Hhdr Hmtx Hres Hlm Hp").
  iIntros "Hhdr Hmtx Hres Hlm Hp".
  iApply ("Hcont" with "Hp").
Qed.

End domain.

(** Sealed for clients, now that the proofs above are done. *)
#[global] Opaque domain٠spawn domain٠join.
