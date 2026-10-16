(** * Semantics of Mizzle's language

    Forked from Zoo ([zoo/language/]). Departures: [Emit] records an
    observation; [atomicity] does not affect steps; own [prim_step]/[nsteps],
    not an Iris [language]. Evaluation is right-to-left, as in Zoo. *)

From stdpp Require Import
  gmap.

From mizzle.lang Require Import
  prelude.
From mizzle.lang Require Export
  syntax.
From mizzle.lang Require Import
  options.

Implicit Types b : bool.
Implicit Types tag sz : nat.
Implicit Types n m : Z.
Implicit Types l : location.
Implicit Types gen : generativity.
Implicit Types mut : mutability.
Implicit Types atm : atomicity.
Implicit Types lit : literal.
Implicit Types x : binder.
Implicit Types e : expr.
Implicit Types es : list expr.
Implicit Types v w : val.
Implicit Types vs : list val.
Implicit Types br : branch.
Implicit Types brs : list branch.
Implicit Types rec : recursive.
Implicit Types recs : list recursive.

Definition thread_id :=
  nat.
Implicit Types tid : thread_id.


Definition val_immediate v :=
  match v with
  | ValLit lit =>
      match lit with
      | LitBool _
      | LitInt _ =>
          true
      | _ =>
          false
      end
  | ValRecs _ _ =>
      false
  | ValBlock _ _ [] =>
      true
  | ValBlock _ _ _ =>
      false
  end.
#[global] Arguments val_immediate !_ / : assert.

Definition eval_unop op v :=
  match op, v with
  | UnopNeg, ValBool b =>
      Some $ ValBool (￢ b)
  | UnopMinus, ValInt n =>
      Some $ ValInt (- n)
  | UnopIsImmediate, v =>
      Some $ ValBool (val_immediate v)
  | _, _ =>
      None
  end.
#[global] Arguments eval_unop !_ !_ / : assert.

Definition eval_binop_int op n1 n2 :=
  match op with
  | BinopPlus =>
      LitInt (n1 + n2)
  | BinopMinus =>
      LitInt (n1 - n2)
  | BinopMult =>
      LitInt (n1 * n2)
  | BinopQuot =>
      LitInt (n1 `quot` n2)
  | BinopRem =>
      LitInt (n1 `rem` n2)
  | BinopLand =>
      LitInt (Z.land n1 n2)
  | BinopLor =>
      LitInt (Z.lor n1 n2)
  | BinopLsl =>
      LitInt (n1 ≪ n2)
  | BinopLsr =>
      LitInt (n1 ≫ n2)
  | BinopLe =>
      LitBool (bool_decide (n1 ≤ n2))
  | BinopLt =>
      LitBool (bool_decide (n1 < n2))
  | BinopGe =>
      LitBool (bool_decide (n1 >= n2))
  | BinopGt =>
      LitBool (bool_decide (n1 > n2))
  end%Z.
#[global] Arguments eval_binop_int !_ _ _ / : assert.
Definition eval_binop op v1 v2 :=
  match v1, v2 with
  | ValInt n1, ValInt n2 =>
      Some $ ValLit $ eval_binop_int op n1 n2
  | _, _ =>
      None
  end.
#[global] Arguments eval_binop _ !_ !_ / : assert.

Definition eval_app_aux recs i rec :=
  subst' rec.1.1 (ValRecs i recs).
Definition eval_app' {A} foldri recs x v e : A :=
  foldri (eval_app_aux recs) (subst' x v e).
Definition eval_app recs x v e :=
  eval_app' foldri recs x v e recs.

Variant subject :=
  | SubjectLoc l
  | SubjectBlock gen vs.
Implicit Types subj : subject.

Definition subject_to_val tag subj :=
  match subj with
  | SubjectLoc l =>
      ValLoc l
  | SubjectBlock gen vs =>
      ValBlock gen tag vs
  end.

Fixpoint eval_match tag sz subj x_fb e_fb brs :=
  match brs with
  | [] =>
      Some $ subst' x_fb (subject_to_val tag subj) e_fb
  | br :: brs =>
      let pat := br.1 in
      if pat.(pattern_tag) ≟ tag && length pat.(pattern_fields) ≟ sz then
        let res := subst' pat.(pattern_as) (subject_to_val tag subj) br.2 in
        match subj with
        | SubjectLoc l =>
            if forallb (BAnon ≟.) pat.(pattern_fields) then
              Some res
            else
              None
        | SubjectBlock _ vs =>
            Some $ subst_list pat.(pattern_fields) vs res
        end
      else
        eval_match tag sz subj x_fb e_fb brs
  end.
#[global] Arguments eval_match _ _ !_ _ _ !_ / : assert.

(** An observation is the value an [Emit] recorded.  Observations are ghost:
    they accumulate in the trace threaded by [prim_step] and no program can
    read them back. *)
Definition observation : Set :=
  val.

Inductive base_step tid : expr → state → list observation → expr → state → list expr → Prop :=
  | base_step_rec f x e σ :
      base_step
        tid
        (Rec f x e)
        σ
        []
        (Val $ ValRec f x e)
        σ
        []
  | base_step_app i recs rec v σ :
      recs !! i = Some rec →
      base_step
        tid
        (App (Val $ ValRecs i recs) (Val v))
        σ
        []
        (eval_app recs rec.1.2 v rec.2)
        σ
        []
  | base_step_let x v1 e2 σ :
      base_step
        tid
        (Let x (Val v1) e2)
        σ
        []
        (subst' x v1 e2)
        σ
        []
  | base_step_unop op v v' σ :
      eval_unop op v = Some v' →
      base_step
        tid
        (Unop op $ Val v)
        σ
        []
        (Val v')
        σ
        []
  | base_step_binop op v1 v2 v' σ :
      eval_binop op v1 v2 = Some v' →
      base_step
        tid
        (Binop op (Val v1) (Val v2))
        σ
        []
        (Val v')
        σ
        []
  | base_step_equal_fail v1 v2 σ :
      v1 ≉ v2 →
      base_step
        tid
        (Equal (Val v1) (Val v2))
        σ
        []
        (Val $ ValBool false)
        σ
        []
  | base_step_equal_success v1 v2 σ :
      v1 ≈ v2 →
      base_step
        tid
        (Equal (Val v1) (Val v2))
        σ
        []
        (Val $ ValBool true)
        σ
        []
  | base_step_if b e1 e2 σ :
      base_step
        tid
        (If (Val $ ValBool b) e1 e2)
        σ
        []
        (if b then e1 else e2)
        σ
        []
  | base_step_while e0 e1 σ :
      base_step
        tid
        (While e0 e1)
        σ
        []
        (If e0 (Seq e1 (While e0 e1)) Unit)
        σ
        []
  | base_step_for n1 n2 e σ :
      base_step
        tid
        (For (Val $ ValInt n1) (Val $ ValInt n2) e)
        σ
        []
        (if decide (n2 ≤ n1)%Z then Unit else Seq (App e (Val $ ValInt n1)) (For (Val $ ValInt (n1 + 1)) (Val $ ValInt n2) e))
        σ
        []
  | base_step_alloc tag n σ l :
      (0 ≤ n)%Z →
      state_alloc_condition l ₊n σ →
      base_step
        tid
        (Alloc (Val $ ValNat tag) (Val $ ValInt n))
        σ
        []
        (Val $ ValLoc l)
        (state_alloc l (Header tag ₊n) (replicate ₊n ValUnit) σ)
        []
  | base_step_block_mutable tag es vs σ l :
      0 < length es →
      es = of_vals vs →
      state_alloc_condition l (length es) σ →
      base_step
        tid
        (Block Mutable tag es)
        σ
        []
        (Val $ ValLoc l)
        (state_alloc l (Header tag (length es)) vs σ)
        []
  | base_step_block_immutable_nongenerative tag es vs σ :
      es = of_vals vs →
      base_step
        tid
        (Block ImmutableNongenerative tag es)
        σ
        []
        (Val $ ValBlock Nongenerative tag vs)
        σ
        []
  | base_step_block_immutable_generative_weak tag es vs σ :
      es = of_vals vs →
      base_step
        tid
        (Block ImmutableGenerativeWeak tag es)
        σ
        []
        (Val $ ValBlock (Generative None) tag vs)
        σ
        []
  | base_step_block_immutable_generative_strong tag es vs σ bid :
      es = of_vals vs →
      base_step
        tid
        (Block ImmutableGenerativeStrong tag es)
        σ
        []
        (Val $ ValBlock (Generative (Some bid)) tag vs)
        σ
        []
  | base_step_match_mutable l hdr x e brs e' σ :
      σ.(state_headers) !! l = Some hdr →
      eval_match hdr.(header_tag) hdr.(header_size) (SubjectLoc l) x e brs = Some e' →
      base_step
        tid
        (Match (Val $ ValLoc l) x e brs)
        σ
        []
        e'
        σ
        []
  | base_step_match_immutable gen tag vs x e brs e' σ :
      eval_match tag (length vs) (SubjectBlock gen vs) x e brs = Some e' →
      base_step
        tid
        (Match (Val $ ValBlock gen tag vs) x e brs)
        σ
        []
        e'
        σ
        []
  | base_step_get_tag_mutable l hdr σ :
      σ.(state_headers) !! l = Some hdr →
      base_step
        tid
        (GetTag $ Val $ ValLoc l)
        σ
        []
        (Val $ ValNat hdr.(header_tag))
        σ
        []
  | base_step_get_tag_immutable gen tag vs σ :
      0 < length vs →
      base_step
        tid
        (GetTag $ Val $ ValBlock gen tag vs)
        σ
        []
        (Val $ ValNat tag)
        σ
        []
  | base_step_get_size_mutable l hdr σ :
      σ.(state_headers) !! l = Some hdr →
      base_step
        tid
        (GetSize $ Val $ ValLoc l)
        σ
        []
        (Val $ ValNat hdr.(header_size))
        σ
        []
  | base_step_get_size_immutable gen tag vs σ :
      0 < length vs →
      base_step
        tid
        (GetSize $ Val $ ValBlock gen tag vs)
        σ
        []
        (Val $ ValNat (length vs))
        σ
        []
  (** The three field rules are quantified over [atm]: an [Atomic] access
      and a [NotAtomic] one take exactly the same step.  Atomicity is not
      operationally observable in a sequentially consistent interleaving
      semantics; the flag exists purely so [logic/race.v] can require a
      non-atomic participant in a race. *)
  | base_step_get_field_mutable atm l fld v σ :
      σ.(state_heap) !! (l +ₗ fld) = Some v →
      base_step
        tid
        (GetField atm (Val $ ValLoc l) (Val $ ValInt fld))
        σ
        []
        (Val v)
        σ
        []
  | base_step_get_field_immutable atm gen tag vs (fld : nat) v σ :
      vs !! fld = Some v →
      base_step
        tid
        (GetField atm (Val $ ValBlock gen tag vs) (Val $ ValNat fld))
        σ
        []
        (Val v)
        σ
        []
  | base_step_set_field atm l fld v σ :
      is_Some (σ.(state_heap) !! (l +ₗ fld)) →
      base_step
        tid
        (SetField atm (Val $ ValLoc l) (Val $ ValInt fld) (Val v))
        σ
        []
        Unit
        (state_set_location (l +ₗ fld) v σ)
        []
  | base_step_xchg l fld v w σ :
      σ.(state_heap) !! (l +ₗ fld) = Some w →
      base_step
        tid
        (Xchg (Val $ ValTuple [ValLoc l; ValInt fld]) (Val v))
        σ
        []
        (Val w)
        (state_set_location (l +ₗ fld) v σ)
        []
  | base_step_cas_fail l fld v1 v2 v σ :
      σ.(state_heap) !! (l +ₗ fld) = Some v →
      v ≉ v1 →
      base_step
        tid
        (CAS (Val $ ValTuple [ValLoc l; ValInt fld]) (Val v1) (Val v2))
        σ
        []
        (Val $ ValBool false)
        σ
        []
  | base_step_cas_success l fld v1 v2 v σ :
      σ.(state_heap) !! (l +ₗ fld) = Some v →
      v ≈ v1 →
      base_step
        tid
        (CAS (Val $ ValTuple [ValLoc l; ValInt fld]) (Val v1) (Val v2))
        σ
        []
        (Val $ ValBool true)
        (state_set_location (l +ₗ fld) v2 σ)
        []
  | base_step_faa l fld n m σ :
      σ.(state_heap) !! (l +ₗ fld) = Some $ ValInt m →
      base_step
        tid
        (FAA (Val $ ValTuple [ValLoc l; ValInt fld]) (Val $ ValInt n))
        σ
        []
        (Val $ ValInt m)
        (state_set_location (l +ₗ fld) (ValInt (m + n)) σ)
        []
  | base_step_fork e σ v :
      val_immediate v →
      base_step
        tid
        (Fork e)
        σ
        []
        Unit
        (state_add_local v σ)
        [e]
  | base_step_get_local v σ :
      σ.(state_locals) !! tid = Some v →
      base_step
        tid
        GetLocal
        σ
        []
        (Val v)
        σ
        []
  | base_step_set_local v σ :
      is_Some (σ.(state_locals) !! tid) →
      base_step
        tid
        (SetLocal (Val v))
        σ
        []
        Unit
        (state_set_local tid v σ)
        []
  | base_step_emit v σ :
      base_step
        tid
        (Emit (Val v))
        σ
        [v]
        Unit
        σ
        [].

Lemma base_step_alloc' tid tag n σ :
  let l := state_fresh σ in
  (0 ≤ n)%Z →
  base_step
    tid
    (Alloc (Val $ ValNat tag) (Val $ ValInt n))
    σ
    []
    (Val $ ValLoc l)
    (state_alloc l (Header tag ₊n) (replicate ₊n ValUnit) σ)
    [].
Proof.
  intros l Hn.
  apply base_step_alloc. 1: done.
  apply state_alloc_condition_fresh.
Qed.
Lemma base_step_block_mutable' tid tag es vs σ :
  let l := state_fresh σ in
  0 < length es →
  es = of_vals vs →
  base_step
    tid
    (Block Mutable tag es)
    σ
    []
    (Val $ ValLoc l)
    (state_alloc l (Header tag (length es)) vs σ)
    [].
Proof.
  intros l Hn ->.
  apply base_step_block_mutable. 1,2: done.
  apply state_alloc_condition_fresh.
Qed.
Lemma base_step_block_immutable_generative_strong' tid tag es vs σ :
  es = of_vals vs →
  base_step
    tid
    (Block ImmutableGenerativeStrong tag es)
    σ
    []
    (Val $ ValBlock (Generative (Some inhabitant)) tag vs)
    σ
    [].
Proof.
  apply base_step_block_immutable_generative_strong.
Qed.
Lemma base_step_fork' tid e σ :
  base_step
    tid
    (Fork e)
    σ
    []
    Unit
    (state_add_local inhabitant σ)
    [e].
Proof.
  apply base_step_fork. done.
Qed.

(** ** Evaluation contexts *)

Inductive ectxi :=
  | CtxApp1 v2
  | CtxApp2 e1
  | CtxLet x e2
  | CtxUnop (op : unop)
  | CtxBinop1 (op : binop) v2
  | CtxBinop2 (op : binop) e1
  | CtxEqual1 v2
  | CtxEqual2 e1
  | CtxIf e1 e2
  | CtxFor1 e2 e3
  | CtxFor2 v1 e3
  | CtxAlloc1 v2
  | CtxAlloc2 e1
  | CtxBlock mut tag es vs
  | CtxMatch x e1 brs
  | CtxGetTag
  | CtxGetSize
  | CtxGetField1 atm v2
  | CtxGetField2 atm e1
  | CtxSetField1 atm v2 v3
  | CtxSetField2 atm e1 v3
  | CtxSetField3 atm e1 e2
  | CtxXchg1 v2
  | CtxXchg2 e1
  | CtxCAS0 v1 v2
  | CtxCAS1 e0 v2
  | CtxCAS2 e0 e1
  | CtxFAA1 v2
  | CtxFAA2 e1
  | CtxSetLocal
  | CtxEmit.
Implicit Types k : ectxi.

Notation CtxSeq := (
  CtxLet BAnon
)(only parsing
).
Notation CtxTuple := (
  CtxBlock ImmutableNongenerative 0
)(only parsing
).

Definition filli k e : expr :=
  match k with
  | CtxApp1 v2 =>
      App e $ Val v2
  | CtxApp2 e1 =>
      App e1 e
  | CtxLet x e2 =>
      Let x e e2
  | CtxUnop op =>
      Unop op e
  | CtxBinop1 op v2 =>
      Binop op e $ Val v2
  | CtxBinop2 op e1 =>
      Binop op e1 e
  | CtxEqual1 v2 =>
      Equal e $ Val v2
  | CtxEqual2 e1 =>
      Equal e1 e
  | CtxIf e1 e2 =>
      If e e1 e2
  | CtxFor1 e2 e3 =>
      For e e2 e3
  | CtxFor2 v1 e3 =>
      For (Val v1) e e3
  | CtxAlloc1 v2 =>
      Alloc e $ Val v2
  | CtxAlloc2 e1 =>
      Alloc e1 e
  | CtxBlock mut tag es vs =>
      Block mut tag $ es ++ e :: of_vals vs
  | CtxMatch x e1 brs =>
      Match e x e1 brs
  | CtxGetTag =>
      GetTag e
  | CtxGetSize =>
      GetSize e
  | CtxGetField1 atm v2 =>
      GetField atm e (Val v2)
  | CtxGetField2 atm e1 =>
      GetField atm e1 e
  | CtxSetField1 atm v2 v3 =>
      SetField atm e (Val v2) (Val v3)
  | CtxSetField2 atm e1 v3 =>
      SetField atm e1 e (Val v3)
  | CtxSetField3 atm e1 e2 =>
      SetField atm e1 e2 e
  | CtxXchg1 v2 =>
      Xchg e $ Val v2
  | CtxXchg2 e1 =>
      Xchg e1 e
  | CtxCAS0 v1 v2 =>
      CAS e (Val v1) (Val v2)
  | CtxCAS1 e0 v2 =>
      CAS e0 e $ Val v2
  | CtxCAS2 e0 e1 =>
      CAS e0 e1 e
  | CtxFAA1 v2 =>
      FAA e $ Val v2
  | CtxFAA2 e1 =>
      FAA e1 e
  | CtxSetLocal =>
      SetLocal e
  | CtxEmit =>
      Emit e
  end.
#[global] Arguments filli !_ _ / : assert.

Definition ectx :=
  list ectxi.

Definition fill K e :=
  foldl (flip filli) e K.

Definition config : Type :=
  list expr * state.

(** ** Step relations *)

Implicit Types σ : state.
Implicit Types κ κs : list observation.
Implicit Types K : ectx.
Implicit Types ρ : config.



Class AsVal e v :=
  as_val : of_val v = e.

Variant prim_step tid e1 σ1 κ e2 σ2 es : Prop :=
  | base_step_fill_prim_step' K e1' e2' :
      e1 = fill K e1' →
      e2 = fill K e2' →
      base_step tid e1' σ1 κ e2' σ2 es →
      prim_step tid e1 σ1 κ e2 σ2 es.
#[global] Arguments base_step_fill_prim_step' {_ _ _ _ _ _ _}.

Definition step ρ1 κ ρ2 :=
  ∃ tid e1 e2 σ2 es,
  prim_step tid e1 ρ1.2 κ e2 σ2 es ∧
  ρ1.1 !! tid = Some e1 ∧
  ρ2 = (<[tid := e2]> ρ1.1 ++ es, σ2).

Inductive nsteps : nat → config → list observation → config → Prop :=
  | nsteps_refl ρ :
     nsteps 0 ρ [] ρ
  | nsteps_l (n : nat) ρ1 ρ2 ρ3 κ κs :
     step ρ1 κ ρ2 →
     nsteps n ρ2 κs ρ3 →
     nsteps (S n) ρ1 (κ ++ κs) ρ3.
#[local] Hint Constructors nsteps : core.

Definition silent_step ρ1 ρ2 :=
  ∃ κ,
  step ρ1 κ ρ2.

Definition base_reducible tid e σ :=
  ∃ κ e' σ' es,
  base_step tid e σ κ e' σ' es.
Definition base_reducible_no_obs tid e σ :=
  ∃ e' σ' es,
  base_step tid e σ [] e' σ' es.
Definition base_irreducible tid e σ :=
  ∀ κ e' σ' es,
  ¬ base_step tid e σ κ e' σ' es.
Definition base_stuck tid e σ :=
  to_val e = None ∧
  base_irreducible tid e σ.
Record pure_base_step e1 e2 :=
  { pure_base_step_safe tid σ1 :
      base_reducible_no_obs tid e1 σ1
  ; pure_base_step_det tid σ1 κ e2' σ2 es :
      base_step tid e1 σ1 κ e2' σ2 es →
        κ = [] ∧
        σ2 = σ1 ∧
        e2' = e2 ∧
        es = []
  }.

Definition reducible tid e σ :=
  ∃ κ e' σ' es,
  prim_step tid e σ κ e' σ' es.
Definition reducible_no_obs tid e σ :=
  ∃ e' σ' es,
  prim_step tid e σ [] e' σ' es.
Definition irreducible tid e σ :=
  ∀ κ e' σ' es,
  ¬ prim_step tid e σ κ e' σ' es.
Definition stuck tid e σ :=
  to_val e = None ∧
  irreducible tid e σ.
Definition not_stuck tid e σ :=
  is_Some (to_val e) ∨
  reducible tid e σ.
Record pure_step e1 e2 :=
  { pure_step_safe tid σ1 :
      reducible_no_obs tid e1 σ1
  ; pure_step_det tid σ1 κ e2' σ2 es :
      prim_step tid e1 σ1 κ e2' σ2 es →
        κ = [] ∧
        σ2 = σ1 ∧
        e2' = e2 ∧
        es = []
  }.

Class Context (K : expr → expr) :=
  { context_fill_not_val e :
      to_val e = None →
      to_val (K e) = None
  ; context_fill_step tid e1 σ1 κ e2 σ2 es :
      prim_step tid e1 σ1 κ e2 σ2 es →
      prim_step tid (K e1) σ1 κ (K e2) σ2 es
  ; context_fill_step_inv tid e1' σ1 κ e2 σ2 es :
      to_val e1' = None →
      prim_step tid (K e1') σ1 κ e2 σ2 es →
        ∃ e2',
        e2 = K e2' ∧
        prim_step tid e1' σ1 κ e2' σ2 es
  }.

Class PureExec (ϕ : Prop) (n : nat) e1 e2 :=
  pure_exec :
    ϕ →
    relations.nsteps pure_step n e1 e2.

Definition sub_redexes_are_values e :=
  ∀ K e', e = fill K e' →
  to_val e' = None →
  K = [].

#[global] Instance filli_inj k :
  Inj (=) (=) (filli k).
Proof.
  induction k; intros ?*; naive_solver.
Qed.
Lemma filli_val k e :
  is_Some (to_val (filli k e)) →
  is_Some (to_val e).
Proof.
  intros (v & ?). destruct k; done.
Qed.
Lemma filli_no_val_inj k1 e1 k2 e2 :
  to_val e1 = None →
  to_val e2 = None →
  filli k1 e1 = filli k2 e2 →
  k1 = k2.
Proof.
  move: k1.
  induction k2; intros k1; destruct k1; try naive_solver.
  intros H1 H2 [= -> -> H%app_inj_2]; first naive_solver.
  simpl. do 3 f_equal.
  apply (f_equal reverse) in H.
  rewrite !reverse_app !reverse_cons -!fmap_reverse /= in H.
  match goal with |- ?vs1 = ?vs2 =>
    apply (inj reverse);
    remember (reverse vs1) as vs1';
    remember (reverse vs2) as vs2';
    clear- H1 H2 H; move: vs2' H; induction vs1'; intros []; naive_solver
  end.
Qed.
Lemma base_step_filli_val tid k e σ1 κ e2 σ2 es :
  base_step tid (filli k e) σ1 κ e2 σ2 es →
  is_Some (to_val e).
Proof.
  move: κ e2.
  induction k; try (inversion_clear 1; eauto || done).
  all: inversion_clear 1.
  all:
    match goal with H: _ ++ _ :: of_vals ?vs1 = of_vals ?vs2 |- _ =>
      apply (f_equal reverse) in H;
      rewrite reverse_app reverse_cons -!fmap_reverse /= in H;
      remember (reverse vs1) as vs1';
      remember (reverse vs2) as vs2';
      clear- H; move: vs2' H; induction vs1'; intros []; naive_solver
    end.
Qed.

#[global] Instance fill_inj K :
  Inj (=) (=) (fill K).
Proof.
  induction K as [| k K IH].
  all: rewrite /Inj.
  all: naive_solver.
Qed.
Lemma fill_nil e :
  fill [] e = e.
Proof.
  done.
Qed.
Lemma fill_app K1 K2 e :
  fill (K1 ++ K2) e = fill K2 (fill K1 e).
Proof.
  apply foldl_app.
Qed.
Lemma fill_val K e :
  is_Some (to_val (fill K e)) →
  is_Some (to_val e).
Proof.
  move: e. induction K as [| k K IH] => e //=.
  intros ?%IH%filli_val => //.
Qed.
Lemma fill_not_val K e :
  to_val e = None →
  to_val (fill K e) = None.
Proof.
  rewrite !eq_None_not_Some.
  eauto using fill_val.
Qed.

Lemma base_step_not_val tid e1 σ1 κ e2 σ2 es :
  base_step tid e1 σ1 κ e2 σ2 es →
  to_val e1 = None.
Proof.
  destruct 1; naive_solver.
Qed.
Lemma step_by_val tid K1 K2 e1 e2 σ1 κ e2' σ2 es :
  fill K1 e1 = fill K2 e2 →
  to_val e1 = None →
  base_step tid e2 σ1 κ e2' σ2 es →
    ∃ K,
    K2 = K ++ K1.
Proof.
  intros Hfill Hred Hstep.
  move: K2 Hfill. induction K1 as [| k1 K1 IH] using rev_ind => /= K2 Hfill.
  - eauto using app_nil_r.
  - destruct K2 as [| k2 K2 _] using rev_ind; simplify_eq/=.
    { rewrite fill_app in Hstep. apply base_step_filli_val in Hstep.
      apply fill_val in Hstep. apply not_eq_None_Some in Hstep. done.
    }
    rewrite !fill_app /= in Hfill.
    assert (k1 = k2) as ->.
    { eapply filli_no_val_inj, Hfill.
      all: eauto using fill_not_val, base_step_not_val.
    }
    simplify_eq. destruct (IH K2) as [K ->]; auto.
    exists K. rewrite assoc //.
Qed.
Lemma base_step_fill_val tid K e σ1 κ e2 σ2 es :
  base_step tid (fill K e) σ1 κ e2 σ2 es →
    is_Some (to_val e) ∨
    K = [].
Proof.
  destruct K as [| k K _] using rev_ind; simpl; first by auto.
  rewrite fill_app /=. intros ?%base_step_filli_val.
  eauto using fill_val.
Qed.

Lemma base_reducible_no_obs_base_reducible tid e σ :
  base_reducible_no_obs tid e σ →
  base_reducible tid e σ.
Proof.
  intros (? & ? & ? & ?). eexists. eauto.
Qed.

Lemma base_step_prim_step tid e1 σ1 κ e2 σ2 es :
  base_step tid e1 σ1 κ e2 σ2 es →
  prim_step tid e1 σ1 κ e2 σ2 es.
Proof.
  apply (base_step_fill_prim_step' []).
  all: rewrite ?fill_nil //.
Qed.
Lemma prim_step_not_val tid e σ κ e' σ' es :
  prim_step tid e σ κ e' σ' es →
  to_val e = None.
Proof.
  intros [? ? ? -> -> ?%base_step_not_val].
  apply eq_None_not_Some. intros ?%fill_val%eq_None_not_Some; done.
Qed.
Lemma reducible_not_val tid e σ :
  reducible tid e σ →
  to_val e = None.
Proof.
  intros (? & ? & ? & ? & ?).
  eauto using prim_step_not_val.
Qed.
Lemma reducible_no_obs_reducible tid e σ :
  reducible_no_obs tid e σ →
  reducible tid e σ.
Proof.
  intros (? & ? & ? & ?).
  eexists. eauto.
Qed.
Lemma base_reducible_reducible tid e σ :
  base_reducible tid e σ →
  reducible tid e σ.
Proof.
  intros (κ & e' & σ' & es & ?).
  exists κ, e', σ', es.
  apply base_step_prim_step. done.
Qed.

Lemma base_reducible_fill_prim_step tid K e1 σ1 κ e2 σ2 es :
  base_reducible tid e1 σ1 →
  prim_step tid (fill K e1) σ1 κ e2 σ2 es →
    ∃ e2',
    e2 = fill K e2' ∧
    base_step tid e1 σ1 κ e2' σ2 es.
Proof.
  intros (κ' & e2'' & σ2'' & es'' & HhstepK) [K' e1' e2' HKe1 -> Hstep].
  edestruct (step_by_val tid K) as [K'' ?]; eauto using base_step_not_val; simplify_eq/=.
  rewrite fill_app in HKe1; simplify_eq.
  exists (fill K'' e2'). rewrite fill_app; split; first done.
  apply base_step_fill_val in HhstepK as [[v ?] | ?]; simplify_eq.
  { apply base_step_not_val in Hstep. simplify_eq. }
  rewrite !fill_nil //.
Qed.
Lemma base_reducible_prim_step tid e1 σ1 κ e2 σ2 es :
  base_reducible tid e1 σ1 →
  prim_step tid e1 σ1 κ e2 σ2 es →
  base_step tid e1 σ1 κ e2 σ2 es.
Proof.
  intros.
  edestruct (base_reducible_fill_prim_step tid []) as (? & ? & ?).
  all: rewrite ?fill_nil; eauto.
  simplify. done.
Qed.

Lemma pure_base_step_pure_step e1 e2 :
  pure_base_step e1 e2 →
  pure_step e1 e2.
Proof.
  intros [Hsafe Hdet]. split.
  - intros tid σ.
    destruct (Hsafe tid σ) as (e2' & σ2 & es & ?).
    exists e2', σ2, es.
    apply base_step_prim_step. done.
  - intros tid σ1 κ e2' σ2 es ?%base_reducible_prim_step.
    all: eauto using base_reducible_no_obs_base_reducible.
Qed.

#[global] Instance context_id :
  Context (@id expr).
Proof.
  constructor; naive_solver.
Qed.
#[global] Instance context_fill K :
  Context (fill K).
Proof.
  split => /=.
  - auto using fill_not_val.
  - intros ? ? ? ? ? ? ? [K' e1' e2' Heq1 Heq2 Hstep].
    exists (K' ++ K) e1' e2'.
    all: rewrite ?Heq1 ?Heq2 ?fill_app //.
  - intros tid e1 σ1 κ e2 σ2 es Hnval [K'' e1'' e2'' Heq1 -> Hstep].
    destruct (step_by_val tid K K'' e1 e1'' σ1 κ e2'' σ2 es) as [K' ->]; try done.
    rewrite fill_app in Heq1. apply (inj (fill _)) in Heq1.
    exists (fill K' e2''). rewrite fill_app. split; first done.
    eauto using prim_step.
Qed.
#[global] Instance context_filli k :
  Context (filli k).
Proof.
  change (Context (fill [k])). apply _.
Qed.

Lemma reducible_context (K : expr → expr) `{!Context K} tid e σ :
  reducible tid e σ →
  reducible tid (K e) σ.
Proof.
  rewrite /reducible.
  naive_solver eauto using context_fill_step.
Qed.
Lemma pure_step_context (K : expr → expr) `{!Context K} e1 e2 :
  pure_step e1 e2 →
  pure_step (K e1) (K e2).
Proof.
  intros [Hred Hstep]. split.
  - rewrite /reducible_no_obs in Hred |- *. naive_solver eauto using context_fill_step.
  - intros tid σ1 κ e2' σ2 es Hpstep.
    destruct (context_fill_step_inv tid e1 σ1 κ e2' σ2 es) as (e2'' & -> & ?); [|exact Hpstep|].
    + destruct (Hred tid σ1) as (? & ? & ? & ?); eauto using prim_step_not_val.
    + edestruct (Hstep tid σ1 κ e2'' σ2 es) as (? & -> & -> & ->); done.
Qed.
Lemma sub_redexes_are_values_alt e :
  ( ∀ k e',
    e = filli k e' →
    is_Some (to_val e')
  ) →
  sub_redexes_are_values e.
Proof.
  intros H K e' ->.
  destruct K as [| k K _] using rev_ind => //=.
  intros []%eq_None_not_Some.
  eapply fill_val, H. rewrite fill_app //.
Qed.

Lemma base_reducible_no_obs_equal tid v1 v2 σ :
  base_reducible_no_obs tid (Equal (Val v1) (Val v2)) σ.
Proof.
  destruct (val_similar_or_nonsimilar v1 v2).
  all: repeat econstructor; done.
Qed.
Lemma base_reducible_equal tid v1 v2 σ :
  base_reducible tid (Equal (Val v1) (Val v2)) σ.
Proof.
  apply base_reducible_no_obs_base_reducible, base_reducible_no_obs_equal.
Qed.
Lemma reducible_equal tid v1 v2 σ :
  reducible tid (Equal (Val v1) (Val v2)) σ.
Proof.
  apply base_reducible_reducible, base_reducible_equal.
Qed.

Lemma base_reducible_no_obs_cas tid l fld v1 v2 v σ :
  σ.(state_heap) !! (l +ₗ fld) = Some v →
  base_reducible_no_obs tid (CAS (Val $ ValTuple [ValLoc l; ValInt fld]) (Val v1) (Val v2)) σ.
Proof.
  destruct (val_similar_or_nonsimilar v v1).
  all: repeat econstructor; done.
Qed.
Lemma base_reducible_cas tid l fld v1 v2 v σ :
  σ.(state_heap) !! (l +ₗ fld) = Some v →
  base_reducible tid (CAS (Val $ ValTuple [ValLoc l; ValInt fld]) (Val v1) (Val v2)) σ.
Proof.
  intros.
  eapply base_reducible_no_obs_base_reducible, base_reducible_no_obs_cas. done.
Qed.
Lemma reducible_cas tid l fld v1 v2 v σ :
  σ.(state_heap) !! (l +ₗ fld) = Some v →
  reducible tid (CAS (Val $ ValTuple [ValLoc l; ValInt fld]) (Val v1) (Val v2)) σ.
Proof.
  intros.
  eapply base_reducible_reducible, base_reducible_cas. done.
Qed.
