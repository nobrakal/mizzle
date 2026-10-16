From iris.proofmode Require Import base proofmode.

From mizzle.lang Require Export semantics.
From mizzle.lang Require Import instances.

From mizzle.logic Require Import interp goal stuck.

(** * Focused goal-mode lemmas

    [goal.v] states each lemma over [running p (fill ks e)]. The lemmas in
    this file restate the same content with the explicit notation
    [focused p ks e ≜ running p (fill ks e)], so that proofs read in terms
    of "thread [p], focused at [e] under context [ks]". The [focused_bind]
    lemma lets one push an inner evaluation context [K] from the expression
    onto the [ks] stack — the analog of [wp_bind]. *)

Notation focused p ks e := (running p (fill ks e)).

Section focused.
Context `{seqlogGS Σ}.

(** ** Focus / unfocus

    Push an inner evaluation context [K] sitting in the expression onto the
    outer context [ks] (and back). *)
Lemma focused_bind K p ks e :
  focused p ks (fill K e) ⊣⊢ focused p (K ++ ks) e.
Proof. by rewrite -fill_app. Qed.

(** Forward-direction wand of [focused_bind], used by the [g_focus] tactic
    to push [K] from the focused expression onto the [ks] stack. *)
Lemma focused_bind_l K p ks e :
  focused p ks (fill K e) -∗ focused p (K ++ ks) e.
Proof. iIntros "Hp". by rewrite focused_bind. Qed.

(** ** Per-primitive lemmas

    Each takes a [focused p ks ...] hypothesis and returns
    [focused p ks ...] in the continuation: the [ks] is preserved across
    the step, so chaining steps requires no [ks] bookkeeping. *)

Lemma focused_pure_step E p ks e e' φ n :
  PureExec φ n e e' →
  φ →
  focused p ks e -∗
  (focused p ks e' -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hexec Hφ) "Hp Hcont".
  iApply (goal_pure_step _ _ _ _ _ _ _ Hexec Hφ with "Hp Hcont").
Qed.

(** ** [For]-loop steps

    The two cases of the underlying [pure_for] step, leaving the induction
    to the caller.

    Case 1: the bound is reached ([n ≤ lo]); the loop reduces to [()]. *)
Lemma focused_for_done E p ks (lo n:Z) (body:expr) :
  (n ≤ lo)%Z →
  focused p ks (For (Val (ValInt lo)) (Val (ValInt n)) body) -∗
  (focused p ks (Val ValUnit) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hle) "Hf Hcont".
  iApply (focused_pure_step _ _ _ _ _ _ _ (pure_for lo n body) with "Hf").
  - done.
  - iIntros "Hf". rewrite decide_True //. iApply ("Hcont" with "Hf").
Qed.

(** Case 2: one more iteration ([lo < n]); the loop reduces to running the
    body on [lo], then continuing the loop from [lo + 1]. *)
Lemma focused_for_step E p ks (lo n:Z) (body:expr) :
  (lo < n)%Z →
  focused p ks (For (Val (ValInt lo)) (Val (ValInt n)) body) -∗
  (focused p ks
     (Seq (App body (Val (ValInt lo)))
          (For (Val (ValInt (lo + 1))) (Val (ValInt n)) body)) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hlt) "Hf Hcont".
  iApply (focused_pure_step _ _ _ _ _ _ _ (pure_for lo n body) with "Hf").
  - done.
  - iIntros "Hf". case_decide; [lia|]. iApply ("Hcont" with "Hf").
Qed.

(** "At K" forms of the two [For] cases ([g_for] itself uses the
    context-free forms above, after [g_locate]). *)
Lemma focused_for_done_at E K p ks (lo n:Z) (body:expr) :
  (n ≤ lo)%Z →
  focused p ks (fill K (For (Val (ValInt lo)) (Val (ValInt n)) body)) -∗
  (focused p ks (fill K (Val ValUnit)) -∗ goal E) -∗
  goal E.
Proof.
  rewrite -!fill_app.
  iIntros (Hle) "Hf Hcont".
  iApply (focused_for_done _ _ _ _ _ _ Hle with "Hf Hcont").
Qed.

Lemma focused_for_step_at E K p ks (lo n:Z) (body:expr) :
  (lo < n)%Z →
  focused p ks (fill K (For (Val (ValInt lo)) (Val (ValInt n)) body)) -∗
  (focused p ks
     (fill K (Seq (App body (Val (ValInt lo)))
                  (For (Val (ValInt (lo + 1))) (Val (ValInt n)) body))) -∗ goal E) -∗
  goal E.
Proof.
  rewrite -!fill_app.
  iIntros (Hlt) "Hf Hcont".
  iApply (focused_for_step _ _ _ _ _ _ Hlt with "Hf Hcont").
Qed.

(** ** [While]-loop step

    The underlying [pure_while] step unfolds one iteration: the condition
    guards the body, followed by the loop again. *)
Lemma focused_while E p ks (e0 e1:expr) :
  focused p ks (While e0 e1) -∗
  (focused p ks (If e0 (Seq e1 (While e0 e1)) (Val ValUnit)) -∗ goal E) -∗
  goal E.
Proof.
  iIntros "Hf Hcont".
  iApply (focused_pure_step _ _ _ _ _ _ _ (pure_while e0 e1) with "Hf Hcont").
  done.
Qed.

Lemma focused_while_at E K p ks (e0 e1:expr) :
  focused p ks (fill K (While e0 e1)) -∗
  (focused p ks (fill K (If e0 (Seq e1 (While e0 e1)) (Val ValUnit))) -∗ goal E) -∗
  goal E.
Proof.
  rewrite -!fill_app.
  iApply focused_while.
Qed.

Lemma focused_alloc E p ks v :
  focused p ks (ref (Val v)) -∗
  (∀ l:location, l ↦∗ [v] -∗ focused p ks (Val (ValLoc l)) -∗ goal E) -∗
  goal E.
Proof.
  iIntros "Hp Hcont".
  iApply (goal_ref with "Hp Hcont").
Qed.

Lemma focused_get_field E p ks (l:location) (fld:Z) dq vs v (atm : atomicity) :
  (0 ≤ fld)%Z → vs !! Z.to_nat fld = Some v →
  focused p ks (GetField atm (Val (ValLoc l)) (Val (ValInt fld))) -∗
  l ↦∗{dq} vs -∗
  (l ↦∗{dq} vs -∗ focused p ks (Val v) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hfld Hidx) "Hp Hl Hcont".
  iApply (goal_get_field _ _ _ _ _ _ _ _ _ Hfld Hidx with "Hp Hl Hcont").
Qed.

Lemma focused_set_field E p ks (l:location) (fld:Z) v w vs (atm : atomicity) :
  (0 ≤ fld)%Z → vs !! Z.to_nat fld = Some v →
  focused p ks (SetField atm (Val (ValLoc l)) (Val (ValInt fld)) (Val w)) -∗
  l ↦∗ vs -∗
  (l ↦∗ <[Z.to_nat fld := w]> vs -∗ focused p ks (Val ValUnit) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hfld Hidx) "Hp Hl Hcont".
  iApply (goal_set_field _ _ _ _ _ _ _ _ _ Hfld Hidx with "Hp Hl Hcont").
Qed.

Lemma focused_cas_succ E p ks (l:location) (fld:Z) v1 v2 vl vs :
  vl ≈ v1 → (0 ≤ fld)%Z → vs !! Z.to_nat fld = Some vl →
  focused p ks (CAS (Val (ValTuple [ValLoc l; ValInt fld])) (Val v1) (Val v2)) -∗
  l ↦∗ vs -∗
  (l ↦∗ <[Z.to_nat fld := v2]> vs -∗ focused p ks (Val (ValBool true)) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hsim Hfld Hidx) "Hp Hl Hcont".
  iApply (goal_cas_succ _ _ _ _ _ _ _ _ _ Hsim Hfld Hidx with "Hp Hl Hcont").
Qed.

Lemma focused_cas_fail E p ks (l:location) (fld:Z) dq v1 v2 vl vs :
  vl ≉ v1 → (0 ≤ fld)%Z → vs !! Z.to_nat fld = Some vl →
  focused p ks (CAS (Val (ValTuple [ValLoc l; ValInt fld])) (Val v1) (Val v2)) -∗
  l ↦∗{dq} vs -∗
  (l ↦∗{dq} vs -∗ focused p ks (Val (ValBool false)) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hnsim Hfld Hidx) "Hp Hl Hcont".
  iApply (goal_cas_fail _ _ _ _ _ _ _ _ _ _ Hnsim Hfld Hidx with "Hp Hl Hcont").
Qed.

Lemma focused_equal_fail E p ks v1 v2 :
  v1 ≉ v2 →
  focused p ks (Equal (Val v1) (Val v2)) -∗
  (focused p ks (Val (ValBool false)) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hnsim) "Hp Hcont".
  iApply (goal_equal_fail _ _ _ _ _ Hnsim with "Hp Hcont").
Qed.

Lemma focused_equal_succ E p ks v1 v2 :
  v1 ≈ v2 →
  focused p ks (Equal (Val v1) (Val v2)) -∗
  (focused p ks (Val (ValBool true)) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hsim) "Hp Hcont".
  iApply (goal_equal_succ _ _ _ _ _ Hsim with "Hp Hcont").
Qed.

Lemma focused_xchg E p ks (l:location) (fld:Z) v w vs :
  (0 ≤ fld)%Z → vs !! Z.to_nat fld = Some v →
  focused p ks (Xchg (Val (ValTuple [ValLoc l; ValInt fld])) (Val w)) -∗
  l ↦∗ vs -∗
  (l ↦∗ <[Z.to_nat fld := w]> vs -∗ focused p ks (Val v) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hfld Hidx) "Hp Hl Hcont".
  iApply (goal_xchg _ _ _ _ _ _ _ _ Hfld Hidx with "Hp Hl Hcont").
Qed.

Lemma focused_faa E p ks (l:location) (fld:Z) (i1 i2:Z) vs :
  (0 ≤ fld)%Z → vs !! Z.to_nat fld = Some (ValInt i1) →
  focused p ks (FAA (Val (ValTuple [ValLoc l; ValInt fld])) (Val (ValInt i2))) -∗
  l ↦∗ vs -∗
  (l ↦∗ <[Z.to_nat fld := ValInt (i1 + i2)]> vs -∗ focused p ks (Val (ValInt i1)) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hfld Hidx) "Hp Hl Hcont".
  iApply (goal_faa _ _ _ _ _ _ _ _ Hfld Hidx with "Hp Hl Hcont").
Qed.

Lemma focused_get_local E p ks v :
  focused p ks GetLocal -∗
  local p v -∗
  (local p v -∗ focused p ks (Val v) -∗ goal E) -∗
  goal E.
Proof.
  iIntros "Hp Hloc Hcont".
  iApply (goal_get_local with "Hp Hloc Hcont").
Qed.

Lemma focused_set_local E p ks v w :
  focused p ks (SetLocal (Val w)) -∗
  local p v -∗
  (local p w -∗ focused p ks (Val ValUnit) -∗ goal E) -∗
  goal E.
Proof.
  iIntros "Hp Hloc Hcont".
  iApply (goal_set_local with "Hp Hloc Hcont").
Qed.

Lemma focused_match_mutable E p ks (l:location) hdr x e0 brs e' dq :
  eval_match hdr.(header_tag) hdr.(header_size) (SubjectLoc l) x e0 brs = Some e' →
  focused p ks (Match (Val (ValLoc l)) x e0 brs) -∗
  l ↦ₕ{dq} hdr -∗
  (l ↦ₕ{dq} hdr -∗ focused p ks e' -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hev) "Hp Hl Hcont".
  iApply (goal_match_mutable with "Hp Hl Hcont"); done.
Qed.

Lemma focused_get_tag_mutable E p ks (l:location) hdr dq :
  focused p ks (GetTag (Val (ValLoc l))) -∗
  l ↦ₕ{dq} hdr -∗
  (l ↦ₕ{dq} hdr -∗ focused p ks (Val (ValNat hdr.(header_tag))) -∗ goal E) -∗
  goal E.
Proof.
  iIntros "Hp Hl Hcont".
  iApply (goal_get_tag_mutable with "Hp Hl Hcont").
Qed.

Lemma focused_get_size_mutable E p ks (l:location) hdr dq :
  focused p ks (GetSize (Val (ValLoc l))) -∗
  l ↦ₕ{dq} hdr -∗
  (l ↦ₕ{dq} hdr -∗ focused p ks (Val (ValNat hdr.(header_size))) -∗ goal E) -∗
  goal E.
Proof.
  iIntros "Hp Hl Hcont".
  iApply (goal_get_size_mutable with "Hp Hl Hcont").
Qed.

(** A spawned thread starts at the empty context [[]]. The fork takes a
    fresh domain-local seed value [v] (which must be immediate). *)
Lemma focused_fork E p ks e v :
  val_immediate v →
  focused p ks (Fork e) -∗
  (∀ p':nat, local p' v -∗ focused p' [] e -∗ focused p ks (Val ValUnit) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hv) "Hp Hcont".
  iApply (goal_fork _ _ _ _ v Hv with "Hp").
  iIntros (p') "Hloc Hp' Hpme".
  iApply ("Hcont" $! p' with "Hloc Hp' Hpme").
Qed.

(** ** Variants with an inner evaluation context [K]

    These restate the per-primitive lemmas with an extra [fill K] surrounding
    the redex. After [reshape_expr] decomposes the focused expression into
    [fill K e_redex], the matching [_at] lemma applies with [K] supplied,
    and the resulting hypothesis stays in [focused p ks (fill K (Val v))]
    form — [simpl] then collapses it back to a concrete expression. The
    pure tactics ([g_pure], [g_rec], [g_call], …) use these; the effectful
    ones instead [g_locate] the redex and apply the context-free lemma. *)

Lemma focused_pure_step_at E K p ks e e' φ n :
  PureExec φ n e e' →
  φ →
  focused p ks (fill K e) -∗
  (focused p ks (fill K e') -∗ goal E) -∗
  goal E.
Proof.
  rewrite -!fill_app.
  iIntros (Hexec Hφ) "Hp Hcont".
  iApply (goal_pure_step _ _ _ _ _ _ _ Hexec Hφ with "Hp Hcont").
Qed.

(** Direct β-reduction and [Rec]-to-value steps. [focused_pure_step_at]
    leaves [PureExec φ n e e'] for [tc_solve], and for the application redex
    that search runs through the loop-prone [AsValRecs] resolution (the
    dominant cost of [g_call]). These two lemmas hand the [PureExec] instance
    in directly — [e'] is computed in the statement — so the tactics that use
    them avoid the typeclass search entirely. *)

(** PureExec for a single (recursive) closure applied to an argument.
    [ValRec]/[ValFun] are both [ValRecs 0 [(f,x,e)]]. *)
Lemma pure_beta f x e v2 :
  PureExec True 1
    (App (Val (ValRec f x e)) (Val v2))
    (subst' f (ValRec f x e) (subst' x v2 e)).
Proof.
  intros _.
  apply (pure_app (ValRec f x e) 0 [(f, x, e)] (f, x, e) [ValRec f x e] v2); done.
Qed.

Lemma focused_beta_at E K p ks f x e v2 :
  focused p ks (fill K (App (Val (ValRec f x e)) (Val v2))) -∗
  (focused p ks (fill K (subst' f (ValRec f x e) (subst' x v2 e))) -∗ goal E) -∗
  goal E.
Proof.
  apply (focused_pure_step_at E K p ks _ _ True 1 (pure_beta f x e v2) I).
Qed.

Lemma focused_rec_at E K p ks f x e :
  focused p ks (fill K (Rec f x e)) -∗
  (focused p ks (fill K (Val (ValRec f x e))) -∗ goal E) -∗
  goal E.
Proof.
  apply (focused_pure_step_at E K p ks _ _ True 1 (pure_rec f x e) I).
Qed.

Lemma focused_alloc_at E K p ks v :
  focused p ks (fill K (ref (Val v))) -∗
  (∀ l:location, l ↦∗ [v] -∗ focused p ks (fill K (Val (ValLoc l))) -∗ goal E) -∗
  goal E.
Proof.
  iIntros "Hp Hcont".
  iEval (rewrite -fill_app) in "Hp".
  iApply (goal_ref with "Hp").
  iIntros (l) "Hl Hpnew".
  iEval (rewrite fill_app) in "Hpnew".
  iApply ("Hcont" $! l with "Hl Hpnew").
Qed.

Lemma focused_get_field_at E K p ks (l:location) (fld:Z) dq vs v (atm : atomicity) :
  (0 ≤ fld)%Z → vs !! Z.to_nat fld = Some v →
  focused p ks (fill K (GetField atm (Val (ValLoc l)) (Val (ValInt fld)))) -∗
  l ↦∗{dq} vs -∗
  (l ↦∗{dq} vs -∗ focused p ks (fill K (Val v)) -∗ goal E) -∗
  goal E.
Proof.
  rewrite -!fill_app.
  iIntros (Hfld Hidx) "Hp Hl Hcont".
  iApply (goal_get_field _ _ _ _ _ _ _ _ _ Hfld Hidx with "Hp Hl Hcont").
Qed.

Lemma focused_set_field_at E K p ks (l:location) (fld:Z) v w vs (atm : atomicity) :
  (0 ≤ fld)%Z → vs !! Z.to_nat fld = Some v →
  focused p ks (fill K (SetField atm (Val (ValLoc l)) (Val (ValInt fld)) (Val w))) -∗
  l ↦∗ vs -∗
  (l ↦∗ <[Z.to_nat fld := w]> vs -∗ focused p ks (fill K (Val ValUnit)) -∗ goal E) -∗
  goal E.
Proof.
  rewrite -!fill_app.
  iIntros (Hfld Hidx) "Hp Hl Hcont".
  iApply (goal_set_field _ _ _ _ _ _ _ _ _ Hfld Hidx with "Hp Hl Hcont").
Qed.

Lemma focused_cas_succ_at E K p ks (l:location) (fld:Z) v1 v2 vl vs :
  vl ≈ v1 → (0 ≤ fld)%Z → vs !! Z.to_nat fld = Some vl →
  focused p ks (fill K (CAS (Val (ValTuple [ValLoc l; ValInt fld])) (Val v1) (Val v2))) -∗
  l ↦∗ vs -∗
  (l ↦∗ <[Z.to_nat fld := v2]> vs -∗ focused p ks (fill K (Val (ValBool true))) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hsim Hfld Hidx) "Hp Hl Hcont".
  iEval (rewrite -fill_app) in "Hp".
  iApply (goal_cas_succ _ _ _ _ _ _ _ _ _ Hsim Hfld Hidx with "Hp Hl").
  iIntros "Hl Hpnew".
  iEval (rewrite fill_app) in "Hpnew".
  iApply ("Hcont" with "Hl Hpnew").
Qed.

Lemma focused_cas_fail_at E K p ks (l:location) (fld:Z) dq v1 v2 vl vs :
  vl ≉ v1 → (0 ≤ fld)%Z → vs !! Z.to_nat fld = Some vl →
  focused p ks (fill K (CAS (Val (ValTuple [ValLoc l; ValInt fld])) (Val v1) (Val v2))) -∗
  l ↦∗{dq} vs -∗
  (l ↦∗{dq} vs -∗ focused p ks (fill K (Val (ValBool false))) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hnsim Hfld Hidx) "Hp Hl Hcont".
  iEval (rewrite -fill_app) in "Hp".
  iApply (goal_cas_fail _ _ _ _ _ _ _ _ _ _ Hnsim Hfld Hidx with "Hp Hl").
  iIntros "Hl Hpnew".
  iEval (rewrite fill_app) in "Hpnew".
  iApply ("Hcont" with "Hl Hpnew").
Qed.

(** ** Header-aware single-cell field lemmas

    Restate [goal_*_cell] in [focused] form, both bare and with an inner
    evaluation context [K]. The array specs carry the persistent
    header [l ↦ₕ{dqh} hdr] separately from individual cells, so these fit
    where the block-based lemmas would force owning the whole array. *)

Lemma focused_get_field_cell E p ks (l:location) (fld:Z) dqh hdr dq v (atm : atomicity) :
  (0 ≤ fld < Z.of_nat (header_size hdr))%Z →
  focused p ks (GetField atm (Val (ValLoc l)) (Val (ValInt fld))) -∗
  l ↦ₕ{dqh} hdr -∗
  (l +ₗ fld) ↦{dq} v -∗
  (l ↦ₕ{dqh} hdr -∗ (l +ₗ fld) ↦{dq} v -∗ focused p ks (Val v) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hfld) "Hp Hh Hc Hcont".
  iApply (goal_get_field_cell _ _ _ _ _ _ _ _ _ _ Hfld with "Hp Hh Hc Hcont").
Qed.

Lemma focused_get_field_cell_at E K p ks (l:location) (fld:Z) dqh hdr dq v (atm : atomicity) :
  (0 ≤ fld < Z.of_nat (header_size hdr))%Z →
  focused p ks (fill K (GetField atm (Val (ValLoc l)) (Val (ValInt fld)))) -∗
  l ↦ₕ{dqh} hdr -∗
  (l +ₗ fld) ↦{dq} v -∗
  (l ↦ₕ{dqh} hdr -∗ (l +ₗ fld) ↦{dq} v -∗ focused p ks (fill K (Val v)) -∗ goal E) -∗
  goal E.
Proof.
  rewrite -!fill_app.
  iIntros (Hfld) "Hp Hh Hc Hcont".
  iApply (goal_get_field_cell _ _ _ _ _ _ _ _ _ _ Hfld with "Hp Hh Hc Hcont").
Qed.

Lemma focused_set_field_cell E p ks (l:location) (fld:Z) dqh hdr v w (atm : atomicity) :
  (0 ≤ fld < Z.of_nat (header_size hdr))%Z →
  focused p ks (SetField atm (Val (ValLoc l)) (Val (ValInt fld)) (Val w)) -∗
  l ↦ₕ{dqh} hdr -∗
  (l +ₗ fld) ↦ v -∗
  (l ↦ₕ{dqh} hdr -∗ (l +ₗ fld) ↦ w -∗ focused p ks (Val ValUnit) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hfld) "Hp Hh Hc Hcont".
  iApply (goal_set_field_cell _ _ _ _ _ _ _ _ _ _ Hfld with "Hp Hh Hc Hcont").
Qed.

Lemma focused_set_field_cell_at E K p ks (l:location) (fld:Z) dqh hdr v w (atm : atomicity) :
  (0 ≤ fld < Z.of_nat (header_size hdr))%Z →
  focused p ks (fill K (SetField atm (Val (ValLoc l)) (Val (ValInt fld)) (Val w))) -∗
  l ↦ₕ{dqh} hdr -∗
  (l +ₗ fld) ↦ v -∗
  (l ↦ₕ{dqh} hdr -∗ (l +ₗ fld) ↦ w -∗ focused p ks (fill K (Val ValUnit)) -∗ goal E) -∗
  goal E.
Proof.
  rewrite -!fill_app.
  iIntros (Hfld) "Hp Hh Hc Hcont".
  iApply (goal_set_field_cell _ _ _ _ _ _ _ _ _ _ Hfld with "Hp Hh Hc Hcont").
Qed.

Lemma focused_cas_succ_cell E p ks (l:location) (fld:Z) dqh hdr v1 v2 vl :
  vl ≈ v1 →
  (0 ≤ fld < Z.of_nat (header_size hdr))%Z →
  focused p ks (CAS (Val (ValTuple [ValLoc l; ValInt fld])) (Val v1) (Val v2)) -∗
  l ↦ₕ{dqh} hdr -∗
  (l +ₗ fld) ↦ vl -∗
  (l ↦ₕ{dqh} hdr -∗ (l +ₗ fld) ↦ v2 -∗ focused p ks (Val (ValBool true)) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hsim Hfld) "Hp Hh Hc Hcont".
  iApply (goal_cas_succ_cell _ _ _ _ _ _ _ _ _ _ Hsim Hfld with "Hp Hh Hc Hcont").
Qed.

Lemma focused_cas_succ_cell_at E K p ks (l:location) (fld:Z) dqh hdr v1 v2 vl :
  vl ≈ v1 →
  (0 ≤ fld < Z.of_nat (header_size hdr))%Z →
  focused p ks (fill K (CAS (Val (ValTuple [ValLoc l; ValInt fld])) (Val v1) (Val v2))) -∗
  l ↦ₕ{dqh} hdr -∗
  (l +ₗ fld) ↦ vl -∗
  (l ↦ₕ{dqh} hdr -∗ (l +ₗ fld) ↦ v2 -∗ focused p ks (fill K (Val (ValBool true))) -∗ goal E) -∗
  goal E.
Proof.
  rewrite -!fill_app.
  iIntros (Hsim Hfld) "Hp Hh Hc Hcont".
  iApply (goal_cas_succ_cell _ _ _ _ _ _ _ _ _ _ Hsim Hfld with "Hp Hh Hc Hcont").
Qed.

Lemma focused_cas_fail_cell E p ks (l:location) (fld:Z) dqh hdr dq v1 v2 vl :
  vl ≉ v1 →
  (0 ≤ fld < Z.of_nat (header_size hdr))%Z →
  focused p ks (CAS (Val (ValTuple [ValLoc l; ValInt fld])) (Val v1) (Val v2)) -∗
  l ↦ₕ{dqh} hdr -∗
  (l +ₗ fld) ↦{dq} vl -∗
  (l ↦ₕ{dqh} hdr -∗ (l +ₗ fld) ↦{dq} vl -∗ focused p ks (Val (ValBool false)) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hnsim Hfld) "Hp Hh Hc Hcont".
  iApply (goal_cas_fail_cell _ _ _ _ _ _ _ _ _ _ _ Hnsim Hfld with "Hp Hh Hc Hcont").
Qed.

Lemma focused_cas_fail_cell_at E K p ks (l:location) (fld:Z) dqh hdr dq v1 v2 vl :
  vl ≉ v1 →
  (0 ≤ fld < Z.of_nat (header_size hdr))%Z →
  focused p ks (fill K (CAS (Val (ValTuple [ValLoc l; ValInt fld])) (Val v1) (Val v2))) -∗
  l ↦ₕ{dqh} hdr -∗
  (l +ₗ fld) ↦{dq} vl -∗
  (l ↦ₕ{dqh} hdr -∗ (l +ₗ fld) ↦{dq} vl -∗ focused p ks (fill K (Val (ValBool false))) -∗ goal E) -∗
  goal E.
Proof.
  rewrite -!fill_app.
  iIntros (Hnsim Hfld) "Hp Hh Hc Hcont".
  iApply (goal_cas_fail_cell _ _ _ _ _ _ _ _ _ _ _ Hnsim Hfld with "Hp Hh Hc Hcont").
Qed.

Lemma focused_fork_at E K p ks e v :
  val_immediate v →
  focused p ks (fill K (Fork e)) -∗
  (∀ p':nat, local p' v -∗ focused p' [] e -∗ focused p ks (fill K (Val ValUnit)) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hv) "Hp Hcont".
  iEval (rewrite -fill_app) in "Hp".
  iApply (goal_fork _ _ _ _ v Hv with "Hp").
  iIntros (p') "Hloc Hp' Hpme".
  iEval (rewrite fill_app) in "Hpme".
  iApply ("Hcont" $! p' with "Hloc Hp' Hpme").
Qed.

(** ** Stuck lemmas

    Each takes a [focused] hypothesis at a stuck redex and produces
    [is_stuck p]. Combine with [fulfill_stuck] below to close [goal ⊤]. *)

Lemma focused_stuck_call p ks v w :
  (match v with ValRecs _ _ => False | _ => True end) →
  focused p ks (App (Val v) (Val w)) -∗
  is_stuck p.
Proof.
  iIntros (Hbad) "Hp".
  iApply (stuck_call with "Hp"). done.
Qed.

Lemma focused_stuck_if p ks v e1 e2 :
  (match v with ValBool _ => False | _ => True end) →
  focused p ks (If (Val v) e1 e2) -∗
  is_stuck p.
Proof.
  iIntros (Hbad) "Hp".
  iApply (stuck_if with "Hp"). done.
Qed.

(** ** Closing [goal ⊤]

    [fulfill_stuck p] closes [goal ⊤] given any [is_stuck p] resource and the
    [remaining is_stuck'] budget. *)
Lemma fulfill_stuck p :
  is_stuck p -∗ remaining is_stuck' -∗ goal ⊤.
Proof.
  iIntros "Hstuck Hrem".
  iApply (fulfill with "[Hstuck Hrem]"); last by iModIntro.
  iApply (update_remaining with "[Hstuck] Hrem").
  iIntros "_". by iExists p.
Qed.

End focused.
