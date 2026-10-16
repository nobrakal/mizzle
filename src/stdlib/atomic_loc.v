From iris.proofmode Require Import base proofmode.
From stdpp Require Import hlist.

From mizzle.lang Require Export semantics.
From mizzle.lang Require Import instances.

From mizzle.logic Require Import interp goal goal_proof goal_tactics.
From mizzle.lang Require Import options.

(** Split-argument forms of the read-modify-write primitives.

    [CAS] / [Xchg] / [FAA] take their target as a single "atomic location"
    descriptor: the two-field tuple [(l, fld)] that Zoo uses to represent
    OCaml's [Atomic.Loc.t], and that the [e.[fld]] notation builds. The
    semantics keeps that shape, because [ocaml2mizzle] passes such descriptors
    around first-class and dropping them would lose [Atomic.Loc.t] support
    (see lang/semantics.v).

    Proving anything about a descriptor written in source form costs a step:
    [e.[fld]] is a [Block] *expression*, so it has to be reduced to a value
    before the [CAS] rule applies -- [g_block] then [g_cas_succ]. These
    wrappers take [l] and [fld] separately and absorb that reduction into
    their specs (below), so hand-written Mizzle code can name
    the target directly and step it in one go. *)

(** A field on its own, as an expression: [⟨contents⟩] is the offset that
    [e.[contents]] would put in the descriptor. Needed because the wrappers
    take the field as an ordinary argument, while field names live in the
    [mizzle_field] custom entry and are otherwise only reachable inside the
    [.[ ]] / [.{ }] / [.< >] notations. *)
Notation "⟨ fld ⟩" := (
  Val (ValInt (Z.of_nat fld))
)(at level 0,
  fld custom mizzle_field,
  format "⟨ fld ⟩"
) : expr_scope.

Definition atomic_loc٠cas : val :=
  vfun: "l" "fld" "v1" "v2" =>
    CAS ("l", "fld") "v1" "v2".

Definition atomic_loc٠xchg : val :=
  vfun: "l" "fld" "v" =>
    Xchg ("l", "fld") "v".

Definition atomic_loc٠faa : val :=
  vfun: "l" "fld" "i" =>
    FAA ("l", "fld") "i".

(** Goal-mode specs for the split-argument accessors above.

    Each one mirrors the corresponding rule of [logic/goal.v] -- same side
    conditions, same footprint -- but takes the target as [#l] and [#fld]
    rather than as an already-reduced descriptor value. Building and reducing
    the [(l, fld)] tuple happens inside the proof, once, so a caller never
    has to interleave [g_block] with the read-modify-write step. *)

Section atomic_loc.
Context `{seqlogGS Σ}.

Notation focused p ks e := (running p (fill ks e)).

(** [atomic_loc٠cas #l #fld v1 v2] when the current contents [vl] match [v1]: the store
    happens and the call returns [true]. *)
Lemma focused_atomic_loc_cas_succ E p ks (l:location) (fld:Z) v1 v2 vl vs :
  vl ≈ v1 →
  (0 ≤ fld)%Z →
  vs !! Z.to_nat fld = Some vl →
  l ↦∗ vs -∗
  focused p ks
    (App (App (App (App (Val atomic_loc٠cas) (Val (ValLoc l))) (Val (ValInt fld)))
      (Val v1)) (Val v2)) -∗
  (l ↦∗ <[Z.to_nat fld := v2]> vs -∗
   focused p ks (Val (ValBool true)) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hsim Hfld Hidx) "Hl Hf Hcont". rewrite /atomic_loc٠cas.
  g_call4 "Hf". g_block "Hf".
  iApply (goal_cas_succ with "Hf Hl"); [done..|].
  iIntros "Hl Hf". iApply ("Hcont" with "Hl Hf").
Qed.

(** [atomic_loc٠cas #l #fld v1 v2] when the current contents [vl] do *not* match: the
    block is untouched and the call returns [false]. Holds at any fraction,
    the access being read-only. *)
Lemma focused_atomic_loc_cas_fail E p ks (l:location) (fld:Z) dq v1 v2 vl vs :
  vl ≉ v1 →
  (0 ≤ fld)%Z →
  vs !! Z.to_nat fld = Some vl →
  l ↦∗{dq} vs -∗
  focused p ks
    (App (App (App (App (Val atomic_loc٠cas) (Val (ValLoc l))) (Val (ValInt fld)))
      (Val v1)) (Val v2)) -∗
  (l ↦∗{dq} vs -∗ focused p ks (Val (ValBool false)) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hnsim Hfld Hidx) "Hl Hf Hcont". rewrite /atomic_loc٠cas.
  g_call4 "Hf". g_block "Hf".
  iApply (goal_cas_fail with "Hf Hl"); [done..|].
  iIntros "Hl Hf". iApply ("Hcont" with "Hl Hf").
Qed.

(** [atomic_loc٠xchg #l #fld w] stores [w] and returns the previous contents. *)
Lemma focused_atomic_loc_xchg E p ks (l:location) (fld:Z) v w vs :
  (0 ≤ fld)%Z →
  vs !! Z.to_nat fld = Some v →
  l ↦∗ vs -∗
  focused p ks
    (App (App (App (Val atomic_loc٠xchg) (Val (ValLoc l))) (Val (ValInt fld))) (Val w)) -∗
  (l ↦∗ <[Z.to_nat fld := w]> vs -∗ focused p ks (Val v) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hfld Hidx) "Hl Hf Hcont". rewrite /atomic_loc٠xchg.
  g_call3 "Hf". g_block "Hf".
  iApply (goal_xchg with "Hf Hl"); [done..|].
  iIntros "Hl Hf". iApply ("Hcont" with "Hl Hf").
Qed.

(** [atomic_loc٠faa #l #fld #i2] adds [i2] to the integer at the target and returns the
    value it had before. *)
Lemma focused_atomic_loc_faa E p ks (l:location) (fld:Z) (i1 i2:Z) vs :
  (0 ≤ fld)%Z →
  vs !! Z.to_nat fld = Some (ValInt i1) →
  l ↦∗ vs -∗
  focused p ks
    (App (App (App (Val atomic_loc٠faa) (Val (ValLoc l))) (Val (ValInt fld)))
      (Val (ValInt i2))) -∗
  (l ↦∗ <[Z.to_nat fld := ValInt (i1 + i2)]> vs -∗
   focused p ks (Val (ValInt i1)) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hfld Hidx) "Hl Hf Hcont". rewrite /atomic_loc٠faa.
  g_call3 "Hf". g_block "Hf".
  iApply (goal_faa with "Hf Hl"); [done..|].
  iIntros "Hl Hf". iApply ("Hcont" with "Hl Hf").
Qed.

(** Under an evaluation context, so the tactics below can fire on a wrapper
    call buried in a [let] or an [if]. Same shape as [goal_assert_at]. *)
Lemma focused_atomic_loc_cas_succ_at K E p ks (l:location) (fld:Z) v1 v2 vl vs :
  vl ≈ v1 →
  (0 ≤ fld)%Z →
  vs !! Z.to_nat fld = Some vl →
  l ↦∗ vs -∗
  focused p ks (fill K
    (App (App (App (App (Val atomic_loc٠cas) (Val (ValLoc l))) (Val (ValInt fld)))
      (Val v1)) (Val v2))) -∗
  (l ↦∗ <[Z.to_nat fld := v2]> vs -∗
   focused p ks (fill K (Val (ValBool true))) -∗ goal E) -∗
  goal E.
Proof. intros. rewrite -!fill_app. iApply focused_atomic_loc_cas_succ; done. Qed.

Lemma focused_atomic_loc_cas_fail_at K E p ks (l:location) (fld:Z) dq v1 v2 vl vs :
  vl ≉ v1 →
  (0 ≤ fld)%Z →
  vs !! Z.to_nat fld = Some vl →
  l ↦∗{dq} vs -∗
  focused p ks (fill K
    (App (App (App (App (Val atomic_loc٠cas) (Val (ValLoc l))) (Val (ValInt fld)))
      (Val v1)) (Val v2))) -∗
  (l ↦∗{dq} vs -∗ focused p ks (fill K (Val (ValBool false))) -∗ goal E) -∗
  goal E.
Proof. intros. rewrite -!fill_app. iApply focused_atomic_loc_cas_fail; done. Qed.

Lemma focused_atomic_loc_xchg_at K E p ks (l:location) (fld:Z) v w vs :
  (0 ≤ fld)%Z →
  vs !! Z.to_nat fld = Some v →
  l ↦∗ vs -∗
  focused p ks (fill K
    (App (App (App (Val atomic_loc٠xchg) (Val (ValLoc l))) (Val (ValInt fld)))
      (Val w))) -∗
  (l ↦∗ <[Z.to_nat fld := w]> vs -∗
   focused p ks (fill K (Val v)) -∗ goal E) -∗
  goal E.
Proof. intros. rewrite -!fill_app. iApply focused_atomic_loc_xchg; done. Qed.

Lemma focused_atomic_loc_faa_at K E p ks (l:location) (fld:Z) (i1 i2:Z) vs :
  (0 ≤ fld)%Z →
  vs !! Z.to_nat fld = Some (ValInt i1) →
  l ↦∗ vs -∗
  focused p ks (fill K
    (App (App (App (Val atomic_loc٠faa) (Val (ValLoc l))) (Val (ValInt fld)))
      (Val (ValInt i2)))) -∗
  (l ↦∗ <[Z.to_nat fld := ValInt (i1 + i2)]> vs -∗
   focused p ks (fill K (Val (ValInt i1))) -∗ goal E) -∗
  goal E.
Proof. intros. rewrite -!fill_app. iApply focused_atomic_loc_faa; done. Qed.

End atomic_loc.

(** Generated code calls the wrappers rather than the primitives, so
    [g_cas_succ] / [g_cas_fail] fire on a wrapper call. Each tries the
    wrapper first and otherwise falls back to the primitive [CAS] form, so a
    proof stepping hand-written code that uses [CAS] directly is unaffected.
    (The primitive-only forms are [g_cas_prim_succ] / [g_cas_prim_fail] of
    [logic/goal_tactics.v]; [Xchg] / [FAA] have no dedicated tactic.) *)

Ltac g_locate_any_cas Hp name :=
  g_locate Hp
    ltac:(fun e' => lazymatch e' with
          | App (App (App (App (Val atomic_loc٠cas) (Val _)) (Val _)) (Val _)) (Val _) => idtac
          | CAS (Val _) (Val _) (Val _) => idtac
          end)
    ltac:(fun e =>
      lazymatch e with
      | context [CAS _ _ _] =>
        g_miss name open_constr:(CAS (Val _) (Val _) (Val _)) open_constr:(CAS _ _ _) e
      | _ =>
        g_miss name open_constr:(App (App (App (App (Val atomic_loc٠cas) (Val _)) (Val _)) (Val _)) (Val _))
                    open_constr:(App (App (App (App (Val atomic_loc٠cas) _) _) _) _) e
      end).

Tactic Notation "g_cas_succ" constr(Hp) constr(Hl) :=
  iStartProof;
  (* Reduce a projection under the target first ([t.<head>] in
     [atomic_loc٠cas t.<head> ⟨contents⟩ ...]), exactly as the primitive form
     needs; the wrapper wants all four operands to be values. *)
  g_reduce_cas_descr Hp;
  g_locate_any_cas Hp "g_cas_succ";
  let intros := mk_intro_2 Hl Hp in
  with_focused_ks_e Hp ltac:(fun ks e =>
    lazymatch e with
    | App (App (App (App (Val atomic_loc٠cas) _) _) _) _ =>
      let spec := mk_spec_2 Hl Hp in
      iApply (ITrm (focused_atomic_loc_cas_succ _ _ ks _ _ _ _ _ _) hnil spec)
    | CAS _ _ _ =>
      let spec := mk_spec_2 Hp Hl in
      iApply (ITrm (focused_cas_succ _ _ ks _ _ _ _ _ _) hnil spec)
    end);
  try g_field_sidecond;
  g_continue intros Hp.

Tactic Notation "g_cas_fail" constr(Hp) constr(Hl) :=
  iStartProof;
  g_reduce_cas_descr Hp;
  g_locate_any_cas Hp "g_cas_fail";
  let intros := mk_intro_2 Hl Hp in
  with_focused_ks_e Hp ltac:(fun ks e =>
    lazymatch e with
    | App (App (App (App (Val atomic_loc٠cas) _) _) _) _ =>
      let spec := mk_spec_2 Hl Hp in
      iApply (ITrm (focused_atomic_loc_cas_fail _ _ ks _ _ _ _ _ _ _) hnil spec)
    | CAS _ _ _ =>
      let spec := mk_spec_2 Hp Hl in
      iApply (ITrm (focused_cas_fail _ _ ks _ _ _ _ _ _ _) hnil spec)
    end);
  try g_field_sidecond;
  try solve_nonsimilar;
  try (lazymatch goal with
       | |- environments.envs_entails _ _ =>
           iIntros intros; iEval (simpl) in Hp
       end).

(** Sealed for clients, now that the proofs above are done. *)
#[global] Opaque atomic_loc٠cas atomic_loc٠xchg atomic_loc٠faa.
