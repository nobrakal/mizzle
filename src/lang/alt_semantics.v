From stdpp Require Import relations.
From mizzle.lang Require Import prelude.
From mizzle.lang Require Import semantics.

From mizzle.logic Require Import decompose wf_access.

(** * Mizzle small-step semantics with bound checks.

    [semantics.v]'s [base_step] lets a mutable field operation
    ([GetField]/[SetField]/[Xchg]/[CAS]/[FAA]) fire as soon as the *physical* cell
    [l +ₗ fld] is present in [state_heap]; it never consults [state_headers]
    to check that [fld] is a legitimate field of the block at [l]. The
    semantics below — [base_step_bc] / [prim_step_bc] / [silent_step_bc] —
    is identical except that every mutable field operation additionally
    requires [fld] to be in bounds w.r.t. the block's header.

    We then prove this bound-checked semantics equivalent to the original
    MizzleLang step refined by the project's out-of-bounds predicate, i.e. to
    [step] (MizzleLang step ∧ [wf_access], with [κ]). *)

(** [fld] is a legitimate field index of the block located at [l]. This is
    exactly the side condition appearing in [wf_access]. *)
Definition in_bounds (σ : state) (l : location) (fld : Z) : Prop :=
  ∃ hdr, σ.(state_headers) !! l = Some hdr ∧
         (0 ≤ fld < Z.of_nat (header_size hdr))%Z.

(** The bound-check predicate on a *redex*. It is the bare-redex counterpart
    of [wf_access] (which matches on [(decompose e).2]); see
    [wf_access_redex] below. *)
Definition bound_check (σ : state) (e : expr) : Prop :=
  match e with
  | GetField  _ (Val (ValLoc l)) (Val (ValInt fld))
  | SetField _ (Val (ValLoc l)) (Val (ValInt fld)) (Val _)
  | Xchg (Val (ValTuple [ValLoc l; ValInt fld])) (Val _)
  | CAS  (Val (ValTuple [ValLoc l; ValInt fld])) (Val _) (Val _)
  | FAA  (Val (ValTuple [ValLoc l; ValInt fld])) (Val (ValInt _)) =>
      in_bounds σ l fld
  | _ => True
  end.

(** ** Bound-checked base step.

    Mirrors [mizzle.lang.semantics.base_step] verbatim, save for the five
    mutable field operations, which gain an [in_bounds] premise. Immutable
    block reads ([base_step_get_field_immutable], on [ValBlock]) need no such
    premise: they index into the value list directly, never the heap, and
    [wf_access] is vacuously [True] on them. [Emit] is a leaf step and
    touches no field, so it needs no premise either. *)
Inductive base_step_bc tid : expr → state → list observation → expr → state → list expr → Prop :=
  | base_step_bc_rec f x e σ :
      base_step_bc tid (Rec f x e) σ [] (Val $ ValRec f x e) σ []
  | base_step_bc_app i recs rec v σ :
      recs !! i = Some rec →
      base_step_bc tid (App (Val $ ValRecs i recs) (Val v)) σ []
        (eval_app recs rec.1.2 v rec.2) σ []
  | base_step_bc_let x v1 e2 σ :
      base_step_bc tid (Let x (Val v1) e2) σ [] (subst' x v1 e2) σ []
  | base_step_bc_unop op v v' σ :
      eval_unop op v = Some v' →
      base_step_bc tid (Unop op $ Val v) σ [] (Val v') σ []
  | base_step_bc_binop op v1 v2 v' σ :
      eval_binop op v1 v2 = Some v' →
      base_step_bc tid (Binop op (Val v1) (Val v2)) σ [] (Val v') σ []
  | base_step_bc_equal_fail v1 v2 σ :
      v1 ≉ v2 →
      base_step_bc tid (Equal (Val v1) (Val v2)) σ [] (Val $ ValBool false) σ []
  | base_step_bc_equal_success v1 v2 σ :
      v1 ≈ v2 →
      base_step_bc tid (Equal (Val v1) (Val v2)) σ [] (Val $ ValBool true) σ []
  | base_step_bc_if b e1 e2 σ :
      base_step_bc tid (If (Val $ ValBool b) e1 e2) σ [] (if b then e1 else e2) σ []
  | base_step_bc_while e0 e1 σ :
      base_step_bc tid (While e0 e1) σ [] (If e0 (Seq e1 (While e0 e1)) Unit) σ []
  | base_step_bc_for n1 n2 e σ :
      base_step_bc tid (For (Val $ ValInt n1) (Val $ ValInt n2) e) σ []
        (if decide (n2 ≤ n1)%Z then Unit else Seq (App e (Val $ ValInt n1)) (For (Val $ ValInt (n1 + 1)) (Val $ ValInt n2) e)) σ []
  | base_step_bc_alloc tag n σ l :
      (0 ≤ n)%Z →
      state_alloc_condition l ₊n σ →
      base_step_bc tid (Alloc (Val $ ValNat tag) (Val $ ValInt n)) σ []
        (Val $ ValLoc l) (state_alloc l (Header tag ₊n) (replicate ₊n ValUnit) σ) []
  | base_step_bc_block_mutable tag es vs σ l :
      0 < length es →
      es = of_vals vs →
      state_alloc_condition l (length es) σ →
      base_step_bc tid (Block Mutable tag es) σ []
        (Val $ ValLoc l) (state_alloc l (Header tag (length es)) vs σ) []
  | base_step_bc_block_immutable_nongenerative tag es vs σ :
      es = of_vals vs →
      base_step_bc tid (Block ImmutableNongenerative tag es) σ []
        (Val $ ValBlock Nongenerative tag vs) σ []
  | base_step_bc_block_immutable_generative_weak tag es vs σ :
      es = of_vals vs →
      base_step_bc tid (Block ImmutableGenerativeWeak tag es) σ []
        (Val $ ValBlock (Generative None) tag vs) σ []
  | base_step_bc_block_immutable_generative_strong tag es vs σ bid :
      es = of_vals vs →
      base_step_bc tid (Block ImmutableGenerativeStrong tag es) σ []
        (Val $ ValBlock (Generative (Some bid)) tag vs) σ []
  | base_step_bc_match_mutable l hdr x e brs e' σ :
      σ.(state_headers) !! l = Some hdr →
      eval_match hdr.(header_tag) hdr.(header_size) (SubjectLoc l) x e brs = Some e' →
      base_step_bc tid (Match (Val $ ValLoc l) x e brs) σ [] e' σ []
  | base_step_bc_match_immutable gen tag vs x e brs e' σ :
      eval_match tag (length vs) (SubjectBlock gen vs) x e brs = Some e' →
      base_step_bc tid (Match (Val $ ValBlock gen tag vs) x e brs) σ [] e' σ []
  | base_step_bc_get_tag_mutable l hdr σ :
      σ.(state_headers) !! l = Some hdr →
      base_step_bc tid (GetTag $ Val $ ValLoc l) σ []
        (Val $ ValNat hdr.(header_tag)) σ []
  | base_step_bc_get_tag_immutable gen tag vs σ :
      0 < length vs →
      base_step_bc tid (GetTag $ Val $ ValBlock gen tag vs) σ []
        (Val $ ValNat tag) σ []
  | base_step_bc_get_size_mutable l hdr σ :
      σ.(state_headers) !! l = Some hdr →
      base_step_bc tid (GetSize $ Val $ ValLoc l) σ []
        (Val $ ValNat hdr.(header_size)) σ []
  | base_step_bc_get_size_immutable gen tag vs σ :
      0 < length vs →
      base_step_bc tid (GetSize $ Val $ ValBlock gen tag vs) σ []
        (Val $ ValNat (length vs)) σ []
  (* --- mutable field operations: bound check added --- *)
  | base_step_bc_get_field_mutable atm l fld v σ :
      σ.(state_heap) !! (l +ₗ fld) = Some v →
      in_bounds σ l fld →
      base_step_bc tid (GetField atm (Val $ ValLoc l) (Val $ ValInt fld)) σ [] (Val v) σ []
  | base_step_bc_get_field_immutable atm gen tag vs (fld : nat) v σ :
      vs !! fld = Some v →
      base_step_bc tid (GetField atm (Val $ ValBlock gen tag vs) (Val $ ValNat fld)) σ [] (Val v) σ []
  | base_step_bc_set_field atm l fld v σ :
      is_Some (σ.(state_heap) !! (l +ₗ fld)) →
      in_bounds σ l fld →
      base_step_bc tid (SetField atm (Val $ ValLoc l) (Val $ ValInt fld) (Val v)) σ []
        Unit (state_set_location (l +ₗ fld) v σ) []
  | base_step_bc_xchg l fld v w σ :
      σ.(state_heap) !! (l +ₗ fld) = Some w →
      in_bounds σ l fld →
      base_step_bc tid (Xchg (Val $ ValTuple [ValLoc l; ValInt fld]) (Val v)) σ []
        (Val w) (state_set_location (l +ₗ fld) v σ) []
  | base_step_bc_cas_fail l fld v1 v2 v σ :
      σ.(state_heap) !! (l +ₗ fld) = Some v →
      v ≉ v1 →
      in_bounds σ l fld →
      base_step_bc tid (CAS (Val $ ValTuple [ValLoc l; ValInt fld]) (Val v1) (Val v2)) σ []
        (Val $ ValBool false) σ []
  | base_step_bc_cas_success l fld v1 v2 v σ :
      σ.(state_heap) !! (l +ₗ fld) = Some v →
      v ≈ v1 →
      in_bounds σ l fld →
      base_step_bc tid (CAS (Val $ ValTuple [ValLoc l; ValInt fld]) (Val v1) (Val v2)) σ []
        (Val $ ValBool true) (state_set_location (l +ₗ fld) v2 σ) []
  | base_step_bc_faa l fld n m σ :
      σ.(state_heap) !! (l +ₗ fld) = Some $ ValInt m →
      in_bounds σ l fld →
      base_step_bc tid (FAA (Val $ ValTuple [ValLoc l; ValInt fld]) (Val $ ValInt n)) σ []
        (Val $ ValInt m) (state_set_location (l +ₗ fld) (ValInt (m + n)) σ) []
  | base_step_bc_fork e σ v :
      val_immediate v →
      base_step_bc tid (Fork e) σ [] Unit (state_add_local v σ) [e]
  | base_step_bc_get_local v σ :
      σ.(state_locals) !! tid = Some v →
      base_step_bc tid GetLocal σ [] (Val v) σ []
  | base_step_bc_set_local v σ :
      is_Some (σ.(state_locals) !! tid) →
      base_step_bc tid (SetLocal (Val v)) σ [] Unit (state_set_local tid v σ) []
  | base_step_bc_emit v σ :
      base_step_bc tid (Emit (Val v)) σ [v] Unit σ [].

(** ** Equivalence at the base-step level.

    The bound-checked base step is exactly the original base step whose
    redex passes [bound_check]. *)
Lemma base_step_bc_iff tid e σ κ e2 σ2 es :
  base_step_bc tid e σ κ e2 σ2 es ↔
  base_step tid e σ κ e2 σ2 es ∧ bound_check σ e.
Proof.
  split.
  - intros Hbc.
    induction Hbc;
      (split; [econstructor; eassumption | simpl; try exact I; assumption]).
  - intros [Hs Hbnd].
    induction Hs; simpl in Hbnd;
      try (econstructor; eassumption);
      econstructor; eassumption.
Qed.

(** [wf_access] on a redex (a non-value that takes no further decomposition
    step) coincides with the bare-redex [bound_check]. *)
Lemma wf_access_redex σ e :
  to_val e = None →
  decompose_step e = None →
  wf_access σ e = bound_check σ e.
Proof.
  intros Hv Hd. unfold wf_access.
  pose proof (decompose_fill_redex [] e Hv Hd) as Hde.
  change (fill [] e) with e in Hde.
  rewrite Hde. reflexivity.
Qed.

(** Every [base_step] redex is a head redex: [decompose_step] exposes no
    further evaluation frame. *)
Lemma base_step_decompose_step_None tid e σ κ e2 σ2 es :
  base_step tid e σ κ e2 σ2 es →
  decompose_step e = None.
Proof.
  induction 1; try reflexivity.
  - (* block_mutable *) subst. simpl. by rewrite split_block_of_vals.
  - (* block_immutable_nongenerative *) subst. simpl. by rewrite split_block_of_vals.
  - (* block_immutable_generative_weak *) subst. simpl. by rewrite split_block_of_vals.
  - (* block_immutable_generative_strong *) subst. simpl. by rewrite split_block_of_vals.
Qed.

(** ** Bound-checked primitive and silent steps. *)
Variant prim_step_bc tid e1 σ1 κ e2 σ2 es : Prop :=
  | base_step_bc_fill_prim_step K e1' e2' :
      e1 = fill K e1' →
      e2 = fill K e2' →
      base_step_bc tid e1' σ1 κ e2' σ2 es →
      prim_step_bc tid e1 σ1 κ e2 σ2 es.

Definition silent_step_bc : relation (list expr * state) :=
  λ ρ1 ρ2,
    ∃ κ tid e1 e2 σ2 efs,
      prim_step_bc tid e1 ρ1.2 κ e2 σ2 efs ∧
      ρ1.1 !! tid = Some e1 ∧
      ρ2 = (<[tid := e2]> ρ1.1 ++ efs, σ2).

(** ** Equivalence at the primitive-step level.

    A bound-checked primitive step is a MizzleLang primitive step whose whole
    redex-in-context is [wf_access] (the project's out-of-bounds predicate). *)
Lemma prim_step_bc_iff tid e1 σ κ e2 σ2 es :
  prim_step_bc tid e1 σ κ e2 σ2 es ↔
  prim_step tid e1 σ κ e2 σ2 es ∧ wf_access σ e1.
Proof.
  split.
  - intros [K r r' -> -> Hbc].
    apply base_step_bc_iff in Hbc as [Hs Hbnd].
    pose proof (base_step_not_val _ _ _ _ _ _ _ Hs) as Hv.
    pose proof (base_step_decompose_step_None _ _ _ _ _ _ _ Hs) as Hd.
    split.
    + by eapply base_step_fill_prim_step'.
    + rewrite (wf_access_fill_eq σ K r Hv Hd).
      by rewrite (wf_access_redex σ r Hv Hd).
  - intros [[K r r' -> -> Hs] Hwf].
    pose proof (base_step_not_val _ _ _ _ _ _ _ Hs) as Hv.
    pose proof (base_step_decompose_step_None _ _ _ _ _ _ _ Hs) as Hd.
    eapply base_step_bc_fill_prim_step; [reflexivity|reflexivity|].
    apply base_step_bc_iff. split; [exact Hs|].
    rewrite <- (wf_access_redex σ r Hv Hd).
    by rewrite <- (wf_access_fill_eq σ K r Hv Hd).
Qed.

(** ** Equivalence at the silent-step level.

    The bound-checked silent step is exactly the original MizzleLang silent step
    refined by "no out-of-bounds access" ([step], with [κ] erased). *)
Theorem silent_step_bc_iff ρ1 ρ2 :
  silent_step_bc ρ1 ρ2 ↔ ∃ κ, step ρ1 κ ρ2.
Proof.
  split.
  - intros (κ & tid & e1 & e2 & σ2 & efs & Hp & Hl & Heq).
    apply prim_step_bc_iff in Hp as [Hp Hwf].
    exists (κ), κ, tid, e1, e2, σ2, efs.
    split_and!; done.
  - intros (o & κ & tid & e1 & e2 & σ2 & efs & Hp & Hl & Heq & Hwf & _).
    exists κ, tid, e1, e2, σ2, efs.
    split_and!; try done.
    by apply prim_step_bc_iff.
Qed.
