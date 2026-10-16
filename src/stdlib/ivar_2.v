From iris.proofmode Require Import base proofmode.

From mizzle.lang Require Export semantics.

From mizzle.logic Require Import interp goal goal_proof goal_tactics.
From mizzle.stdlib Require Import mutex condition.
From mizzle.lang Require Import options.

(** Write-once cells, copied from Zoo's [zoo_std/ivar_2__code.v] and restricted
    to the operations Mizzle uses, plus their callees. The field notations come
    from Zoo's [zoo_std/ivar_2__types.v], inlined here because that file holds
    nothing else. See the specs below for the goal-mode specs. *)

Notation "'mutex'" := (
  in_type "zoo_std.ivar_2.t" 0
)(in custom mizzle_field
).
Notation "'condition'" := (
  in_type "zoo_std.ivar_2.t" 1
)(in custom mizzle_field
).
Notation "'result'" := (
  in_type "zoo_std.ivar_2.t" 2
)(in custom mizzle_field
).

Definition ivar_2٠create : val :=
  vfun: <> =>
    { mutex٠create (), condition٠create (), §None }.

Definition ivar_2٠try_get : val :=
  vfun: "t" =>
    "t".{result}.

Definition ivar_2٠get : val :=
  vfun: "t" =>
    match: ivar_2٠try_get "t" with
    | Some "v" =>
        mutex٠synchronize "t".{mutex} ;;
        "v"
    | None =>
        let: "mtx" := "t".{mutex} in
        let: "cond" := "t".{condition} in
        mutex٠protect
          "mtx"
          (fun: <> =>
             condition٠wait_while
               "cond"
               "mtx"
               (fun: <> => "t".{result} == §None)) ;;
        match: "t".{result} with
        | Some "v" =>
            "v"
        | None =>
            Fail
        end
    end.

Definition ivar_2٠set : val :=
  vfun: "t" "v" =>
    mutex٠protect "t".{mutex} (fun: <> => "t" <-{result} ‘Some( "v" )) ;;
    condition٠notify_all "t".{condition}.

(** Goal-mode specs for [ivar_2] (the write-once cell backing
    domains). An ivar is a 3-field record [{ mutex; condition; result }];
    [result] holds [§None] until it is set to [‘Some(v)]. *)

(** The [option] constructor [Some] as a raw value. *)
Notation IVarSome v := (ValBlock Nongenerative 1 [v]).

Section ivar_2.
Context `{seqlogGS Σ}.

Notation focused p ks e := (running p (fill ks e)).

(** [ivar_2٠create ()] allocates a fresh, unset ivar: the record [l],
    its (unlocked) mutex [lm], the trivial condition [()] and the
    [§None] result. *)
Lemma focused_ivar_2_create E p ks :
  focused p ks (App (Val ivar_2٠create) (Val ValUnit)) -∗
  (∀ (l lm : location),
     l ↦ₕ□ Header 0 3 -∗
     (l +ₗ 0%Z) ↦ ValLoc lm -∗
     (l +ₗ 1%Z) ↦ ValUnit -∗
     (l +ₗ 2%Z) ↦ ValUnit -∗
     lm ↦∗ [ValBool false] -∗
     focused p ks (Val (ValLoc l)) -∗ goal E) -∗
  goal E.
Proof.
  iIntros "Hf Hcont". rewrite /ivar_2٠create. g_call "Hf".
  g_focus (App (Val condition٠create) (Val _)) "Hf".
  iApply (focused_condition_create with "Hf").
  iIntros "Hf". iEval (simpl) in "Hf".
  g_focus (App (Val mutex٠create) (Val _)) "Hf".
  iApply (focused_mutex_create with "Hf").
  iIntros (lm) "Hlm Hf". iEval (simpl) in "Hf".
  g_focus (Block Mutable _ _) "Hf".
  iApply (goal_block_mutable _ _ _ _ [ValLoc lm; ValUnit; ValUnit] with "Hf");
    first (simpl; lia).
  iIntros (l) "Hhdr Hcells Hf". iEval (simpl) in "Hf".
  iDestruct "Hcells" as "(Hmtx & Hcond & Hres & _)".
  iApply ("Hcont" with "Hhdr Hmtx Hcond Hres Hlm Hf").
Qed.

(** [ivar_2٠try_get #l] is a raw load of the [result] field. *)
Lemma focused_ivar_2_try_get E p ks (l:location) dqh dq (w:val) :
  l ↦ₕ{dqh} Header 0 3 -∗
  (l +ₗ 2%Z) ↦{dq} w -∗
  focused p ks (App (Val ivar_2٠try_get) (Val (ValLoc l))) -∗
  (l ↦ₕ{dqh} Header 0 3 -∗ (l +ₗ 2%Z) ↦{dq} w -∗ focused p ks (Val w) -∗ goal E) -∗
  goal E.
Proof.
  iIntros "Hhdr Hres Hf Hcont". rewrite /ivar_2٠try_get. g_call "Hf".
  g_get_field_cell "Hf" "Hhdr" "Hres".
  iApply ("Hcont" with "Hhdr Hres Hf").
Qed.

(** [ivar_2٠set #l v]: under the (free) mutex, overwrite [result] with
    [‘Some(v)] and notify. [w] is the previous content — write-once-ness
    is not enforced by the code, only by how the resources are handed
    out. *)
Lemma focused_ivar_2_set E p ks (l lm:location) (v w cnd : val) dqh :
  l ↦ₕ{dqh} Header 0 3 -∗
  (l +ₗ 0%Z) ↦ ValLoc lm -∗
  (l +ₗ 1%Z) ↦ cnd -∗
  (l +ₗ 2%Z) ↦ w -∗
  lm ↦∗ [ValBool false] -∗
  focused p ks (App (App (Val ivar_2٠set) (Val (ValLoc l))) (Val v)) -∗
  (l ↦ₕ{dqh} Header 0 3 -∗
   (l +ₗ 0%Z) ↦ ValLoc lm -∗
   (l +ₗ 1%Z) ↦ cnd -∗
   (l +ₗ 2%Z) ↦ IVarSome v -∗
   lm ↦∗ [ValBool false] -∗
   focused p ks (Val ValUnit) -∗ goal E) -∗
  goal E.
Proof.
  iIntros "Hhdr Hmtx Hcond Hres Hlm Hf Hcont". rewrite /ivar_2٠set. g_call2 "Hf".
  g_rec "Hf".
  g_get_field_cell "Hf" "Hhdr" "Hmtx".
  g_focus (App (App (Val mutex٠protect) (Val _)) (Val _)) "Hf".
  iApply (focused_mutex_protect with "Hlm Hf").
  iIntros (ks') "Hf Hresume".
  g_call "Hf".
  g_block "Hf".
  g_set_field_cell "Hf" "Hhdr" "Hres".
  iApply ("Hresume" with "Hf").
  iIntros "Hlm Hf". iEval (simpl) in "Hf". g_let "Hf".
  g_get_field_cell "Hf" "Hhdr" "Hcond".
  g_focus (App (Val condition٠notify_all) (Val _)) "Hf".
  iApply (focused_condition_notify_all with "Hf").
  iIntros "Hf". iEval (simpl) in "Hf".
  iApply ("Hcont" with "Hhdr Hmtx Hcond Hres Hlm Hf").
Qed.

(** [ivar_2٠get #l] on an already-set ivar: takes the fast path —
    [try_get] reads [‘Some(v)], a [synchronize] on the mutex, and the
    value is returned. (The unset path busy-waits and is intentionally
    not specced.) *)
Lemma focused_ivar_2_get E p ks (l lm:location) (v:val) dqh dq0 dq2 :
  l ↦ₕ{dqh} Header 0 3 -∗
  (l +ₗ 0%Z) ↦{dq0} ValLoc lm -∗
  (l +ₗ 2%Z) ↦{dq2} IVarSome v -∗
  lm ↦∗ [ValBool false] -∗
  focused p ks (App (Val ivar_2٠get) (Val (ValLoc l))) -∗
  (l ↦ₕ{dqh} Header 0 3 -∗
   (l +ₗ 0%Z) ↦{dq0} ValLoc lm -∗
   (l +ₗ 2%Z) ↦{dq2} IVarSome v -∗
   lm ↦∗ [ValBool false] -∗
   focused p ks (Val v) -∗ goal E) -∗
  goal E.
Proof.
  iIntros "Hhdr Hmtx Hres Hlm Hf Hcont". rewrite /ivar_2٠get. g_call "Hf".
  g_focus (App (Val ivar_2٠try_get) (Val _)) "Hf".
  iApply (focused_ivar_2_try_get with "Hhdr Hres Hf").
  iIntros "Hhdr Hres Hf". iEval (simpl) in "Hf".
  g_match "Hf".
  g_get_field_cell "Hf" "Hhdr" "Hmtx".
  g_focus (App (Val mutex٠synchronize) (Val _)) "Hf".
  iApply (focused_mutex_synchronize with "Hlm Hf").
  iIntros "Hlm Hf". iEval (simpl) in "Hf". g_let "Hf".
  iApply ("Hcont" with "Hhdr Hmtx Hres Hlm Hf").
Qed.

End ivar_2.

(** Sealed for clients, now that the proofs above are done. *)
#[global] Opaque ivar_2٠create ivar_2٠try_get ivar_2٠get ivar_2٠set.
