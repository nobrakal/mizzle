(** * Syntax of Mizzle's language

    Forked from Zoo ([zoo/language/]). Departures: field accesses
    carry an [atomicity] flag; [Emit] replaces prophecies ([Proph], [Resolve]);
    no strings or chars. *)

From stdpp Require Import
  countable
  gmap.

From iris.algebra Require Import
  ofe.

From mizzle.lang Require Import
  prelude.
From mizzle.lang Require Export
  classes
  list.
From mizzle.lang Require Import
  options.

(** ** Locations *)

Open Scope Z_scope.

Record location := Loc
  { location_car : Z
  }.
Add Printing Constructor location.

Canonical location_O {SI : sidx} :=
  leibnizO location.

Lemma location_eq𑁒spec l1 l2 :
  l1 = l2 ↔
  location_car l1 = location_car l2.
Proof.
  destruct l1, l2; naive_solver.
Qed.

#[global] Instance location_inhabited : Inhabited location :=
  populate {| location_car := 0 |}.
#[global] Instance location_eq_dec : EqDecision location :=
  ltac:(solve_decision).
#[global] Instance location_countable :
  Countable location.
Proof.
  refine (inj_countable' location_car Loc _).
  by intros [].
Qed.

#[global] Program Instance location_infinite : Infinite location :=
  inj_infinite (λ p, {| location_car := p |}) (λ l, Some (location_car l)) _.
Next Obligation.
  done.
Qed.

Definition location_add l i :=
  {| location_car := location_car l + i |}.

Notation "l +ₗ i" := (
  location_add l i
)(at level 50,
  left associativity
) : stdpp_scope.

#[global] Instance location_add_inj_1 l :
  Inj (=) (=) (location_add l).
Proof.
  intros ?*. rewrite location_eq𑁒spec /=. lia.
Qed.
#[global] Instance location_add_inj_2 i :
  Inj (=) (=) (λ l, location_add l i).
Proof.
  intros ?*. rewrite location_eq𑁒spec Z.add_cancel_r location_eq𑁒spec //.
Qed.
Lemma location_add_assoc l i j :
  l +ₗ i +ₗ j = l +ₗ (i + j).
Proof.
  rewrite location_eq𑁒spec /=. lia.
Qed.
Lemma location_add_0 l :
  l +ₗ 0 = l.
Proof.
  rewrite location_eq𑁒spec /=; lia.
Qed.

Definition location_fresh (ls : gset location) :=
  {| location_car := set_fold (λ k r, (1 + location_car k) `max` r) 1 ls |}.

Lemma location_fresh_fresh ls i :
  0 ≤ i →
  location_fresh ls +ₗ i ∉ ls.
Proof.
  intros Hi.
  enough (∀ l, l ∈ ls → location_car l < location_car (location_fresh ls) + i).
  { naive_solver lia. }
  apply (set_fold_ind_L (λ r ls, ∀ l, l ∈ ls → (location_car l < r + i))).
  all: set_solver by eauto with lia.
Qed.

#[global] Opaque location_fresh.

Close Scope Z_scope.

(** ** Expressions and values *)

Implicit Types b : bool.
Implicit Types tag : nat.
Implicit Types n : Z.
Implicit Types l : location.

Definition block_id :=
  positive.

Variant mutability :=
  | Mutable
  | ImmutableNongenerative
  | ImmutableGenerativeWeak
  | ImmutableGenerativeStrong.
Implicit Types mut : mutability.

#[global] Instance mutability_eq_dec : EqDecision mutability :=
  ltac:(solve_decision).

Variant generativity :=
  | Generative (bid : option block_id)
  | Nongenerative.
Implicit Types gen : generativity.

#[global] Instance generativity_eq_dec : EqDecision generativity :=
  ltac:(solve_decision).

(** Whether a field access is atomic.  The flag is *not* operationally
    observable: an [Atomic] access and a [NotAtomic] one take exactly the
    same step (see [semantics.v]), because the semantics is a sequentially
    consistent interleaving.  It exists so that [logic/race.v] can tell the
    two apart — a data race needs a non-atomic participant. *)
Variant atomicity :=
  | Atomic
  | NotAtomic.
Implicit Types atm : atomicity.

#[global] Instance atomicity_eq_dec : EqDecision atomicity :=
  ltac:(solve_decision).

Variant literal :=
  | LitBool b
  | LitInt n
  | LitLoc l
  | LitPoison.
Implicit Types lit : literal.

#[global] Instance literal_eq_dec : EqDecision literal :=
  ltac:(solve_decision).

Variant unop :=
  | UnopNeg
  | UnopMinus
  | UnopIsImmediate.

#[global] Instance unop_eq_dec : EqDecision unop :=
  ltac:(solve_decision).

Variant binop :=
  | BinopPlus | BinopMinus | BinopMult | BinopQuot | BinopRem
  | BinopLand | BinopLor | BinopLsl | BinopLsr
  | BinopLe | BinopLt | BinopGe | BinopGt.

#[global] Instance binop_eq_dec : EqDecision binop :=
  ltac:(solve_decision).

Record pattern :=
  { pattern_tag : nat
  ; pattern_fields : list binder
  ; pattern_as : binder
  }.

#[global] Instance pattern_inhabited : Inhabited pattern :=
  populate
    {|pattern_tag := inhabitant
    ; pattern_fields := inhabitant
    ; pattern_as := inhabitant
    |}.
#[global] Instance pattern_eq_dec : EqDecision pattern :=
  ltac:(solve_decision).

Unset Elimination Schemes.
Inductive expr :=
  | Val (v : val)
  | Var (x : string)
  | Rec (f x : binder) (e : expr)
  | App (e1 e2 : expr)
  | Let (x : binder) (e1 e2 : expr)
  | Unop (op : unop) (e : expr)
  | Binop (op : binop) (e1 e2 : expr)
  | Equal (e1 e2 : expr)
  | If (e0 e1 e2 : expr)
  | While (e0 e1 : expr)
  | For (e1 e2 e3 : expr)
  | Alloc (e1 e2 : expr)
  | Block mut tag (es : list expr)
  | Match (e0 : expr) (x : binder) (e1 : expr) (brs : list (pattern * expr))
  | GetTag (e : expr)
  | GetSize (e : expr)
  | GetField atm (e1 e2 : expr)
  | SetField atm (e1 e2 e3 : expr)
  | Xchg (e1 e2 : expr)
  | CAS (e0 e1 e2 : expr)
  | FAA (e1 e2 : expr)
  | Fork (e : expr)
  | GetLocal
  | SetLocal (e : expr)
  | Emit (e : expr)
with val :=
  | ValLit lit
  | ValRecs (i : nat) (recs : list (binder * binder * expr))
  | ValBlock gen tag (vs : list val).
Set Elimination Schemes.
Implicit Types e : expr.
Implicit Types es : list expr.
Implicit Types v : val.
Implicit Types vs : list val.

Notation branch :=
  (pattern * expr)%type.
Implicit Types br : branch.
Implicit Types brs : list branch.

Notation recursive :=
  (binder * binder * expr)%type.
Implicit Types rec : recursive.
Implicit Types recs : list recursive.

Section expr_ind.
  Variable P : expr → Prop.

  Variable HVal :
    ∀ v,
    P (Val v).
  Variable HVar :
    ∀ (x : string),
    P (Var x).
  Variable HRec :
    ∀ f x,
    ∀ e, P e →
    P (Rec f x e).
  Variable HApp :
    ∀ e1, P e1 →
    ∀ e2, P e2 →
    P (App e1 e2).
  Variable HLet :
    ∀ x,
    ∀ e1, P e1 →
    ∀ e2, P e2 →
    P (Let x e1 e2).
  Variable HUnop :
    ∀ op,
    ∀ e, P e →
    P (Unop op e).
  Variable HBinop :
    ∀ op,
    ∀ e1, P e1 →
    ∀ e2, P e2 →
    P (Binop op e1 e2).
  Variable HEqual :
    ∀ e1, P e1 →
    ∀ e2, P e2 →
    P (Equal e1 e2).
  Variable HIf :
    ∀ e0, P e0 →
    ∀ e1, P e1 →
    ∀ e2, P e2 →
    P (If e0 e1 e2).
  Variable HWhile :
    ∀ e0, P e0 →
    ∀ e1, P e1 →
    P (While e0 e1).
  Variable HFor :
    ∀ e1, P e1 →
    ∀ e2, P e2 →
    ∀ e3, P e3 →
    P (For e1 e2 e3).
  Variable HAlloc :
    ∀ e1, P e1 →
    ∀ e2, P e2 →
    P (Alloc e1 e2).
  Variable HBlock :
    ∀ mut tag,
    ∀ es, Forall P es →
    P (Block mut tag es).
  Variable HMatch :
    ∀ e0, P e0 →
    ∀ x,
    ∀ e1, P e1 →
    ∀ brs, Forall (λ br, P br.2) brs →
    P (Match e0 x e1 brs).
  Variable HGetTag :
    ∀ e, P e →
    P (GetTag e).
  Variable HGetSize :
    ∀ e, P e →
    P (GetSize e).
  Variable HGetField :
    ∀ atm,
    ∀ e1, P e1 →
    ∀ e2, P e2 →
    P (GetField atm e1 e2).
  Variable HSetField :
    ∀ atm,
    ∀ e1, P e1 →
    ∀ e2, P e2 →
    ∀ e3, P e3 →
    P (SetField atm e1 e2 e3).
  Variable HXchg :
    ∀ e1, P e1 →
    ∀ e2, P e2 →
    P (Xchg e1 e2).
  Variable HCAS :
    ∀ e0, P e0 →
    ∀ e1, P e1 →
    ∀ e2, P e2 →
    P (CAS e0 e1 e2).
  Variable HFAA :
    ∀ e1, P e1 →
    ∀ e2, P e2 →
    P (FAA e1 e2).
  Variable HFork :
    ∀ e, P e →
    P (Fork e).
  Variable HGetLocal :
    P GetLocal.
  Variable HSetLocal :
    ∀ e, P e →
    P (SetLocal e).
  Variable HEmit :
    ∀ e, P e →
    P (Emit e).

  Fixpoint expr_ind e :=
    match e with
    | Val v =>
        HVal
          v
    | Var x =>
        HVar
          x
    | Rec f x e =>
        HRec
          f x
          e (expr_ind e)
    | App e1 e2 =>
        HApp
          e1 (expr_ind e1)
          e2 (expr_ind e2)
    | Let x e1 e2 =>
        HLet
          x
          e1 (expr_ind e1)
          e2 (expr_ind e2)
    | Unop op e =>
        HUnop
          op
          e (expr_ind e)
    | Binop op e1 e2 =>
        HBinop
          op
          e1 (expr_ind e1)
          e2 (expr_ind e2)
    | Equal e1 e2 =>
        HEqual
          e1 (expr_ind e1)
          e2 (expr_ind e2)
    | If e0 e1 e2 =>
        HIf
          e0 (expr_ind e0)
          e1 (expr_ind e1)
          e2 (expr_ind e2)
    | While e0 e1 =>
        HWhile
          e0 (expr_ind e0)
          e1 (expr_ind e1)
    | For e1 e2 e3 =>
        HFor
          e1 (expr_ind e1)
          e2 (expr_ind e2)
          e3 (expr_ind e3)
    | Alloc e1 e2 =>
        HAlloc
          e1 (expr_ind e1)
          e2 (expr_ind e2)
    | Block mut tag es =>
        HBlock
          mut tag
          es (Forall_true P es expr_ind)
    | Match e0 x e1 brs =>
        HMatch
          e0 (expr_ind e0)
          x
          e1 (expr_ind e1)
          brs (Forall_true (λ br, P br.2) brs (λ br, expr_ind br.2))
    | GetTag e =>
        HGetTag
          e (expr_ind e)
    | GetSize e =>
        HGetSize
          e (expr_ind e)
    | GetField atm e1 e2 =>
        HGetField
          atm
          e1 (expr_ind e1)
          e2 (expr_ind e2)
    | SetField atm e1 e2 e3 =>
        HSetField
          atm
          e1 (expr_ind e1)
          e2 (expr_ind e2)
          e3 (expr_ind e3)
    | Xchg e1 e2 =>
        HXchg
          e1 (expr_ind e1)
          e2 (expr_ind e2)
    | CAS e0 e1 e2 =>
        HCAS
          e0 (expr_ind e0)
          e1 (expr_ind e1)
          e2 (expr_ind e2)
    | FAA e1 e2 =>
        HFAA
          e1 (expr_ind e1)
          e2 (expr_ind e2)
    | Fork e =>
        HFork
          e (expr_ind e)
    | GetLocal =>
        HGetLocal
    | SetLocal e =>
        HSetLocal
          e (expr_ind e)
    | Emit e =>
        HEmit
          e (expr_ind e)
    end.
End expr_ind.

Section val_ind.
  Variable P : val → Prop.

  Variable HValLit :
    ∀ lit,
    P (ValLit lit).
  Variable HValRecs :
    ∀ i recs,
    P (ValRecs i recs).
  Variable HValBlock :
    ∀ gen tag,
    ∀ vs, Forall P vs →
    P (ValBlock gen tag vs).

  Fixpoint val_ind v :=
    match v with
    | ValLit lit =>
        HValLit
          lit
    | ValRecs i recs =>
        HValRecs
          i recs
    | ValBlock gen tag vs =>
        HValBlock
          gen tag
          vs (Forall_true P vs val_ind)
    end.
End val_ind.

Section expr_val_mutind.
  Variable Pexpr : expr → Prop.
  Variable Pval : val → Prop.

  Variable HVal :
    ∀ v, Pval v →
    Pexpr (Val v).
  Variable HVar :
    ∀ (x : string),
    Pexpr (Var x).
  Variable HRec :
    ∀ f x,
    ∀ e, Pexpr e →
    Pexpr (Rec f x e).
  Variable HApp :
    ∀ e1, Pexpr e1 →
    ∀ e2, Pexpr e2 →
    Pexpr (App e1 e2).
  Variable HLet :
    ∀ x,
    ∀ e1, Pexpr e1 →
    ∀ e2, Pexpr e2 →
    Pexpr (Let x e1 e2).
  Variable HUnop :
    ∀ op,
    ∀ e, Pexpr e →
    Pexpr (Unop op e).
  Variable HBinop :
    ∀ op,
    ∀ e1, Pexpr e1 →
    ∀ e2, Pexpr e2 →
    Pexpr (Binop op e1 e2).
  Variable HEqual :
    ∀ e1, Pexpr e1 →
    ∀ e2, Pexpr e2 →
    Pexpr (Equal e1 e2).
  Variable HIf :
    ∀ e0, Pexpr e0 →
    ∀ e1, Pexpr e1 →
    ∀ e2, Pexpr e2 →
    Pexpr (If e0 e1 e2).
  Variable HWhile :
    ∀ e0, Pexpr e0 →
    ∀ e1, Pexpr e1 →
    Pexpr (While e0 e1).
  Variable HFor :
    ∀ e1, Pexpr e1 →
    ∀ e2, Pexpr e2 →
    ∀ e3, Pexpr e3 →
    Pexpr (For e1 e2 e3).
  Variable HAlloc :
    ∀ e1, Pexpr e1 →
    ∀ e2, Pexpr e2 →
    Pexpr (Alloc e1 e2).
  Variable HBlock :
    ∀ mut tag,
    ∀ es, Forall Pexpr es →
    Pexpr (Block mut tag es).
  Variable HMatch :
    ∀ e0, Pexpr e0 →
    ∀ x,
    ∀ e1, Pexpr e1 →
    ∀ brs, Forall (λ br, Pexpr br.2) brs →
    Pexpr (Match e0 x e1 brs).
  Variable HGetTag :
    ∀ e, Pexpr e →
    Pexpr (GetTag e).
  Variable HGetSize :
    ∀ e, Pexpr e →
    Pexpr (GetSize e).
  Variable HGetField :
    ∀ atm,
    ∀ e1, Pexpr e1 →
    ∀ e2, Pexpr e2 →
    Pexpr (GetField atm e1 e2).
  Variable HSetField :
    ∀ atm,
    ∀ e1, Pexpr e1 →
    ∀ e2, Pexpr e2 →
    ∀ e3, Pexpr e3 →
    Pexpr (SetField atm e1 e2 e3).
  Variable HXchg :
    ∀ e1, Pexpr e1 →
    ∀ e2, Pexpr e2 →
    Pexpr (Xchg e1 e2).
  Variable HCAS :
    ∀ e0, Pexpr e0 →
    ∀ e1, Pexpr e1 →
    ∀ e2, Pexpr e2 →
    Pexpr (CAS e0 e1 e2).
  Variable HFAA :
    ∀ e1, Pexpr e1 →
    ∀ e2, Pexpr e2 →
    Pexpr (FAA e1 e2).
  Variable HFork :
    ∀ e, Pexpr e →
    Pexpr (Fork e).
  Variable HGetLocal :
    Pexpr GetLocal.
  Variable HSetLocal :
    ∀ e, Pexpr e →
    Pexpr (SetLocal e).
  Variable HEmit :
    ∀ e, Pexpr e →
    Pexpr (Emit e).

  Variable HValLit :
    ∀ lit,
    Pval (ValLit lit).
  Variable HValRecs :
    ∀ i,
    ∀ recs, Forall (λ rec, Pexpr rec.2) recs →
    Pval (ValRecs i recs).
  Variable HValBlock :
    ∀ gen tag,
    ∀ vs, Forall Pval vs →
    Pval (ValBlock gen tag vs).

  Fixpoint expr_val_ind e :=
    match e with
    | Val v =>
        HVal
          v (val_expr_ind v)
    | Var x =>
        HVar
          x
    | Rec f x e =>
        HRec
          f x
          e (expr_val_ind e)
    | App e1 e2 =>
        HApp
          e1 (expr_val_ind e1)
          e2 (expr_val_ind e2)
    | Let x e1 e2 =>
        HLet
          x
          e1 (expr_val_ind e1)
          e2 (expr_val_ind e2)
    | Unop op e =>
        HUnop
          op
          e (expr_val_ind e)
    | Binop op e1 e2 =>
        HBinop
          op
          e1 (expr_val_ind e1)
          e2 (expr_val_ind e2)
    | Equal e1 e2 =>
        HEqual
          e1 (expr_val_ind e1)
          e2 (expr_val_ind e2)
    | If e0 e1 e2 =>
        HIf
          e0 (expr_val_ind e0)
          e1 (expr_val_ind e1)
          e2 (expr_val_ind e2)
    | While e0 e1 =>
        HWhile
          e0 (expr_val_ind e0)
          e1 (expr_val_ind e1)
    | For e1 e2 e3 =>
        HFor
          e1 (expr_val_ind e1)
          e2 (expr_val_ind e2)
          e3 (expr_val_ind e3)
    | Alloc e1 e2 =>
        HAlloc
          e1 (expr_val_ind e1)
          e2 (expr_val_ind e2)
    | Block mut tag es =>
        HBlock
          mut tag
          es (Forall_true Pexpr es expr_val_ind)
    | Match e0 x e1 brs =>
        HMatch
          e0 (expr_val_ind e0)
          x
          e1 (expr_val_ind e1)
          brs (Forall_true (λ br, Pexpr br.2) brs (λ br, expr_val_ind br.2))
    | GetTag e =>
        HGetTag
          e (expr_val_ind e)
    | GetSize e =>
        HGetSize
          e (expr_val_ind e)
    | GetField atm e1 e2 =>
        HGetField
          atm
          e1 (expr_val_ind e1)
          e2 (expr_val_ind e2)
    | SetField atm e1 e2 e3 =>
        HSetField
          atm
          e1 (expr_val_ind e1)
          e2 (expr_val_ind e2)
          e3 (expr_val_ind e3)
    | Xchg e1 e2 =>
        HXchg
          e1 (expr_val_ind e1)
          e2 (expr_val_ind e2)
    | CAS e0 e1 e2 =>
        HCAS
          e0 (expr_val_ind e0)
          e1 (expr_val_ind e1)
          e2 (expr_val_ind e2)
    | FAA e1 e2 =>
        HFAA
          e1 (expr_val_ind e1)
          e2 (expr_val_ind e2)
    | Fork e =>
        HFork
          e (expr_val_ind e)
    | GetLocal =>
        HGetLocal
    | SetLocal e =>
        HSetLocal
          e (expr_val_ind e)
    | Emit e =>
        HEmit
          e (expr_val_ind e)
    end
  with val_expr_ind v :=
    match v with
    | ValLit lit =>
        HValLit
          lit
    | ValRecs i recs =>
        HValRecs
          i
          recs (Forall_true (λ rec, Pexpr rec.2) recs (λ rec, expr_val_ind rec.2))
    | ValBlock gen tag vs =>
        HValBlock
          gen tag
          vs (Forall_true Pval vs val_expr_ind)
    end.

  Definition expr_val_mutind :=
    conj
      expr_val_ind
      val_expr_ind.
End expr_val_mutind.

Canonical val_O {SI : sidx} :=
  leibnizO val.
Canonical expr_O {SI : sidx} :=
  leibnizO expr.

Notation Fun x e := (
  Rec BAnon x e
)(only parsing
).
Notation ValRec f x e := (
  ValRecs 0
    ( @cons recursive
        ( @pair (prod binder binder) expr
            (@pair binder binder f x)
            e
        )
        (@nil recursive)
    )
)(only parsing
).
Notation ValFun x e := (
  ValRecs 0
    ( @cons recursive
        ( @pair (prod binder binder) expr
            (@pair binder binder BAnon x)
            e
        )
        (@nil recursive)
    )
)(only parsing
).

Notation Seq e1 e2 := (
  Let BAnon e1 e2
)(only parsing
).

Notation ValBool b := (
  ValLit (LitBool b)
)(only parsing
).
Notation ValInt n := (
  ValLit (LitInt n)
)(only parsing
).
Notation ValNat i := (
  ValLit (LitInt (Z.of_nat i))
)(only parsing
).
Notation ValLoc l := (
  ValLit (LitLoc l)
)(only parsing
).
Notation ValPoison := (
  ValLit LitPoison
)(only parsing
).

Notation Tuple := (
  Block ImmutableNongenerative 0
)(only parsing
).
Notation ValTuple := (
  ValBlock Nongenerative 0
)(only parsing
).

Notation ValUnit := (
  ValTuple []
)(only parsing
).
Notation Unit := (
  Val ValUnit
)(only parsing
).

Notation Fail := (
  App Unit Unit
).
Notation Skip := (
  App (Val (ValFun BAnon Unit)) Unit
).

Notation IsImmediate := (
  Unop UnopIsImmediate
).

Definition val_of_int :=
  ValLit ∘ LitInt.

Definition val_to_int v :=
  match v with
  | ValInt n =>
      Some n
  | _ =>
      None
  end.
Notation of_val :=
  Val
( only parsing
).
Definition to_val e :=
  match e with
  | Val v =>
      Some v
  | _ =>
      None
  end.

Lemma to_of_val v :
  to_val (of_val v) = Some v.
Proof.
  by destruct v.
Qed.
Lemma of_to_val e v :
  to_val e = Some v →
  of_val v = e.
Proof.
  destruct e => //=. by intros [= <-].
Qed.
#[global] Instance of_val_inj :
  Inj (=) (=) of_val.
Proof.
  intros ?*. congruence.
Qed.

Definition of_vals vs :=
  of_val <$> vs.
Fixpoint to_vals es :=
  match es with
  | [] =>
      Some []
  | e :: es =>
      v ← to_val e ;
      es ← to_vals es ;
      mret $ v :: es
  end.

Lemma to_of_vals vs :
  to_vals (of_vals vs) = Some vs.
Proof.
  induction vs as [| v vs IH]; first done.
  rewrite /= IH. naive_solver.
Qed.
Lemma of_to_vals es vs :
  to_vals es = Some vs →
  of_vals vs = es.
Proof.
  revert vs. induction es as [| e es IH]; first naive_solver. move=> [| v vs] /= H.
  all: destruct (to_val e) eqn:Heq, (to_vals es); try done.
  invert H.
  f_equal; last naive_solver.
  destruct e; naive_solver.
Qed.
#[global] Instance of_vals_inj :
  Inj (=) (=) of_vals.
Proof.
  apply _.
Qed.
Lemma length_of_vals vs :
  length (of_vals vs) = length vs.
Proof.
  apply length_fmap.
Qed.
Hint Rewrite
  @length_of_vals
: simpl_length.

#[global] Instance val_inhabited : Inhabited val :=
  populate ValUnit.
#[global] Instance expr_inhabited : Inhabited expr :=
  populate (Val inhabitant).
#[global] Instance expr_eq_dec :
  EqDecision expr.
Proof.
  unshelve refine (
    fix go e1 e2 : Decision (e1 = e2) :=
      let fix go_list es1 es2 : Decision (es1 = es2) :=
        match es1, es2 with
        | [], [] =>
            left _
        | e1 :: es1, e2 :: es2 =>
            cast_if_and
              (decide (e1 = e2))
              (decide (es1 = es2))
        | _, _ =>
            right _
        end
      in
      let fix go_branches brs1 brs2 : Decision (brs1 = brs2) :=
        match brs1, brs2 with
        | [], [] =>
            left _
        | (pat1, e1) :: brs1, (pat2, e2) :: brs2 =>
            cast_if_and3
              (decide (pat1 = pat2))
              (decide (e1 = e2))
              (decide (brs1 = brs2))
        | _, _ =>
            right _
        end
      in
      match e1, e2 with
      | Val v1, Val v2 =>
          cast_if
            (decide (v1 = v2))
      | Var x1, Var x2 =>
          cast_if
            (decide (x1 = x2))
      | Rec f1 x1 e1, Rec f2 x2 e2 =>
         cast_if_and3
           (decide (f1 = f2))
           (decide (x1 = x2))
           (decide (e1 = e2))
      | App e11 e12, App e21 e22 =>
          cast_if_and
            (decide (e11 = e21))
            (decide (e12 = e22))
      | Let x1 e11 e12, Let x2 e21 e22 =>
          cast_if_and3
           (decide (x1 = x2))
           (decide (e11 = e21))
           (decide (e12 = e22))
      | Unop op1 e1, Unop op2 e2 =>
          cast_if_and
            (decide (op1 = op2))
            (decide (e1 = e2))
      | Binop op1 e11 e12, Binop op2 e21 e22 =>
         cast_if_and3
           (decide (op1 = op2))
           (decide (e11 = e21))
           (decide (e12 = e22))
      | Equal e11 e12, Equal e21 e22 =>
          cast_if_and
            (decide (e11 = e21))
            (decide (e12 = e22))
      | If e10 e11 e12, If e20 e21 e22 =>
         cast_if_and3
           (decide (e10 = e20))
           (decide (e11 = e21))
           (decide (e12 = e22))
      | While e10 e11, While e20 e21 =>
          cast_if_and
            (decide (e10 = e20))
            (decide (e11 = e21))
      | For e11 e12 e13, For e21 e22 e23 =>
          cast_if_and3
            (decide (e11 = e21))
            (decide (e12 = e22))
            (decide (e13 = e23))
      | Alloc e11 e12, Alloc e21 e22 =>
         cast_if_and
           (decide (e11 = e21))
           (decide (e12 = e22))
      | Block mut1 tag1 es1, Block mut2 tag2 es2 =>
          cast_if_and3
            (decide (mut1 = mut2))
            (decide (tag1 = tag2))
            (decide (es1 = es2))
      | Match e10 x1 e11 brs1, Match e20 x2 e21 brs2 =>
          cast_if_and4
            (decide (e10 = e20))
            (decide (x1 = x2))
            (decide (e11 = e21))
            (decide (brs1 = brs2))
      | GetTag e1, GetTag e2 =>
          cast_if
            (decide (e1 = e2))
      | GetSize e1, GetSize e2 =>
          cast_if
            (decide (e1 = e2))
      | GetField atm1 e11 e12, GetField atm2 e21 e22 =>
          cast_if_and3
            (decide (atm1 = atm2))
            (decide (e11 = e21))
            (decide (e12 = e22))
      | SetField atm1 e11 e12 e13, SetField atm2 e21 e22 e23 =>
         cast_if_and4
           (decide (atm1 = atm2))
           (decide (e11 = e21))
           (decide (e12 = e22))
           (decide (e13 = e23))
      | Xchg e11 e12, Xchg e21 e22 =>
          cast_if_and
            (decide (e11 = e21))
            (decide (e12 = e22))
      | CAS e10 e11 e12, CAS e20 e21 e22 =>
         cast_if_and3
           (decide (e10 = e20))
           (decide (e11 = e21))
           (decide (e12 = e22))
      | FAA e11 e12, FAA e21 e22 =>
         cast_if_and
           (decide (e11 = e21))
           (decide (e12 = e22))
      | Fork e1, Fork e2 =>
          cast_if
            (decide (e1 = e2))
      | GetLocal, GetLocal =>
          left _
      | SetLocal e1, SetLocal e2 =>
          cast_if
            (decide (e1 = e2))
      | Emit e1, Emit e2 =>
          cast_if
            (decide (e1 = e2))
      | _, _ =>
          right _
      end
    with go_val v1 v2 : Decision (v1 = v2) :=
      let fix go_recursives recs1 recs2 : Decision (recs1 = recs2) :=
        match recs1, recs2 with
        | [], [] =>
            left _
        | (bdrs1, e1) :: recs1, (bdrs2, e2) :: recs2 =>
            cast_if_and3
              (decide (bdrs1 = bdrs2))
              (decide (e1 = e2))
              (decide (recs1 = recs2))
        | _, _ =>
            right _
        end
      in
      let fix go_list vs1 vs2 : Decision (vs1 = vs2) :=
        match vs1, vs2 with
        | [], [] =>
            left _
        | v1 :: vs1, v2 :: vs2 =>
            cast_if_and
              (decide (v1 = v2))
              (decide (vs1 = vs2))
        | _, _ =>
            right _
        end
      in
      match v1, v2 with
      | ValLit l1, ValLit l2 =>
          cast_if
            (decide (l1 = l2))
      | ValRecs i1 recs1, ValRecs i2 recs2 =>
          cast_if_and
            (decide (i1 = i2))
            (decide (recs1 = recs2))
      | ValBlock gen1 tag1 vs1, ValBlock gen2 tag2 vs2 =>
          cast_if_and3
            (decide (gen1 = gen2))
            (decide (tag1 = tag2))
            (decide (vs1 = vs2))
      | _, _ =>
          right _
      end
    for go
  ).
  all: try clear go_list.
  all: try clear go_branches.
  all: try clear go_recursives.
  all: clear go go_val.
  all: abstract congruence.
Defined.
#[global] Instance val_eq_dec :
  EqDecision val.
Proof.
  unshelve refine (
    fix go_val v1 v2 : Decision (v1 = v2) :=
      let fix go_recursives recs1 recs2 : Decision (recs1 = recs2) :=
        match recs1, recs2 with
        | [], [] =>
            left _
        | (bdrs1, e1) :: recs1, (bdrs2, e2) :: recs2 =>
            cast_if_and3
              (decide (bdrs1 = bdrs2))
              (decide (e1 = e2))
              (decide (recs1 = recs2))
        | _, _ =>
            right _
        end
      in
      let fix go_list vs1 vs2 : Decision (vs1 = vs2) :=
        match vs1, vs2 with
        | [], [] =>
            left _
        | v1 :: vs1, v2 :: vs2 =>
            cast_if_and
              (decide (v1 = v2))
              (decide (vs1 = vs2))
        | _, _ =>
            right _
        end
      in
      match v1, v2 with
      | ValLit l1, ValLit l2 =>
          cast_if
            (decide (l1 = l2))
      | ValRecs i1 recs1, ValRecs i2 recs2 =>
          cast_if_and
            (decide (i1 = i2))
            (decide (recs1 = recs2))
      | ValBlock gen1 tag1 es1, ValBlock gen2 tag2 es2 =>
          cast_if_and3
            (decide (gen1 = gen2))
            (decide (tag1 = tag2))
            (decide (es1 = es2))
      | _, _ =>
          right _
      end
  ).
  all: clear go_recursives.
  all: try clear go_list.
  all: clear go_val.
  all: abstract congruence.
Defined.

(** ** Scopes *)

Declare Scope expr_scope.
Delimit Scope expr_scope with E.
Bind Scope expr_scope with expr.

Declare Scope val_scope.
Delimit Scope val_scope with V.
Bind Scope val_scope with val.

(** ** Occurrences and substitution *)

Implicit Types env : gmap string val.

Fixpoint subst (x : string) v e :=
  match e with
  | Val _ =>
      e
  | Var y =>
      if x ≟ y then
        Val v
      else
        Var y
  | Rec f y e =>
      Rec
        f y
        ( if BNamed x ≟ f || BNamed x ≟ y then
            e
          else
            subst x v e
        )
  | App e1 e2 =>
      App
        (subst x v e1)
        (subst x v e2)
  | Let y e1 e2 =>
      Let
        y
        (subst x v e1)
        ( if BNamed x ≟ y then
            e2
          else
            subst x v e2
        )
  | Unop op e =>
      Unop
        op
        (subst x v e)
  | Binop op e1 e2 =>
      Binop
        op
        (subst x v e1)
        (subst x v e2)
  | Equal e1 e2 =>
      Equal
        (subst x v e1)
        (subst x v e2)
  | If e0 e1 e2 =>
      If
        (subst x v e0)
        (subst x v e1)
        (subst x v e2)
  | While e0 e1 =>
      While
        (subst x v e0)
        (subst x v e1)
  | For e1 e2 e3 =>
      For
        (subst x v e1)
        (subst x v e2)
        (subst x v e3)
  | Alloc e1 e2 =>
      Alloc
        (subst x v e1)
        (subst x v e2)
  | Block mut tag es =>
      Block
        mut tag
        (subst x v <$> es)
  | Match e0 y e1 brs =>
      Match
        (subst x v e0)
        y
        ( if BNamed x ≟ y then
            e1
          else
            subst x v e1
        )
        ( ( λ br,
              ( br.1,
                if
                  existsb (BNamed x ≟.) br.1.(pattern_fields) ||
                  BNamed x ≟ br.1.(pattern_as)
                then
                  br.2
                else
                  subst x v br.2
              )
          ) <$> brs
        )
  | GetTag e =>
      GetTag
        (subst x v e)
  | GetSize e =>
      GetSize
        (subst x v e)
  | GetField atm e1 e2 =>
      GetField
        atm
        (subst x v e1)
        (subst x v e2)
  | SetField atm e1 e2 e3 =>
      SetField
        atm
        (subst x v e1)
        (subst x v e2)
        (subst x v e3)
  | Xchg e1 e2 =>
      Xchg
        (subst x v e1)
        (subst x v e2)
  | CAS e0 e1 e2 =>
      CAS
        (subst x v e0)
        (subst x v e1)
        (subst x v e2)
  | FAA e1 e2 =>
      FAA
        (subst x v e1)
        (subst x v e2)
  | Fork e =>
      Fork
        (subst x v e)
  | GetLocal =>
      GetLocal
  | SetLocal e =>
      SetLocal
        (subst x v e)
  | Emit e =>
      Emit
        (subst x v e)
  end.
#[global] Arguments subst _ _ !_ / : assert.
Definition subst' x v :=
  match x with
  | BNamed x =>
      subst x v
  | BAnon =>
      id
  end.
#[global] Arguments subst' !_ _ / _ : assert.

Fixpoint subst_list xs vs e :=
  match xs with
  | [] =>
      e
  | x :: xs =>
      match vs with
      | [] =>
          e
      | v :: vs =>
          subst' x v $ subst_list xs vs e
      end
  end.
#[global] Arguments subst_list !_ !_ _ / : assert.

Lemma subst'_val x v1 v2 :
  subst' x v1 (Val v2) = Val v2.
Proof.
  destruct x; done.
Qed.

(** ** States *)

Implicit Types w : val.
Implicit Types h : gmap location val.

Record header := Header
  { header_tag : nat
  ; header_size : nat
  }.
Add Printing Constructor header.

Record state :=
  { state_headers : gmap location header
  ; state_heap : gmap location val
  ; state_locals : list val
  }.
Implicit Types σ : state.

Canonical state_O {SI : sidx} :=
  leibnizO state.

#[global] Instance state_inhabited : Inhabited state :=
  populate
    {|state_headers := inhabitant
    ; state_heap := inhabitant
    ; state_locals := inhabitant
    |}.

Definition state_update_heap f σ :=
  {|state_headers := σ.(state_headers)
  ; state_heap := f σ.(state_heap)
  ; state_locals := σ.(state_locals)
  |}.
Definition state_update_locals f σ :=
  {|state_headers := σ.(state_headers)
  ; state_heap := σ.(state_heap)
  ; state_locals := f σ.(state_locals)
  |}.

Definition state_set_location l v :=
  state_update_heap $ insert l v.
Definition state_set_local tid v :=
  state_update_locals $ insert tid v.
Definition state_add_local v :=
  state_update_locals $ (.++ [v]).

Section chunk.
  Context {A : Type}.

  Implicit Types x y : A.
  Implicit Types xs : list A.
  Implicit Types m : gmap location A.

  Fixpoint chunk l xs : gmap location A :=
    match xs with
    | [] =>
        ∅
    | x :: xs =>
        <[l := x]> (chunk (l +ₗ 1) xs)
    end.
  #[global] Arguments chunk _ !_ / : assert.

  Lemma chunk_lookup l xs 𝑙 y :
    chunk l xs !! 𝑙 = Some y ↔
      ∃ i,
      (0 ≤ i)%Z ∧
      𝑙 = l +ₗ i ∧
      xs !! ₊i = Some y.
  Proof.
    move: l 𝑙. induction xs as [| x xs IH] => l 𝑙 /=.
    - naive_solver.
    - rewrite lookup_insert_Some IH.
      split.
      + intros [(<- & <-) | (Hl & i & Hi & -> & Hlookup)].
        * exists 0.
          rewrite location_add_0.
          naive_solver.
        * exists (1 + i)%Z.
          rewrite location_add_assoc Z.add_1_l Z2Nat.inj_succ //.
          auto with lia.
      + intros (i & ? & -> & Hlookup).
        destruct_decide (i = 0); simplify.
        { rewrite location_add_0. auto. }
        right. split.
        * rewrite -{1}(location_add_0 l).
          naive_solver.
        * assert (₊i = S ₊(i - 1)) as Hi.
          { rewrite -Z2Nat.inj_succ; lia. }
          rewrite Hi /= in Hlookup.
          exists (i - 1)%Z.
          rewrite location_add_assoc Z.add_sub_assoc Z.add_simpl_l.
          auto with lia.
  Qed.
  Lemma chunk_map_disjoint m l xs :
    ( ∀ i,
      i < length xs →
      m !! (l +ₗ i) = None
    ) →
    chunk l xs ##ₘ m.
  Proof.
    intros Hm.
    apply map_disjoint_spec. intros 𝑙 x1 x2 (i & ? & -> & ?%lookup_lt_Some%inj_lt)%chunk_lookup Hlookup.
    ospecialize* (Hm ₊i). 1: lia.
    rewrite Z2Nat.id // in Hm.
    naive_solver.
  Qed.
End chunk.

Definition state_alloc l hdr vs σ :=
  {|state_headers := <[l := hdr]> σ.(state_headers)
  ; state_heap := chunk l vs ∪ σ.(state_heap)
  ; state_locals := σ.(state_locals)
  |}.

Definition state_alloc_condition l sz σ :=
  σ.(state_headers) !! l = None ∧
  σ.(state_heap) !! l = None ∧
    ∀ i,
    i < sz →
      σ.(state_headers) !! (l +ₗ i) = None ∧
      σ.(state_heap) !! (l +ₗ i) = None.

Definition state_fresh_dom σ :=
  dom σ.(state_headers) ∪
  dom σ.(state_heap).
Definition state_fresh σ :=
  location_fresh $ state_fresh_dom σ.

Lemma state_alloc_condition_fresh sz σ :
  state_alloc_condition (state_fresh σ) sz σ.
Proof.
  pose proof (location_fresh_fresh $ state_fresh_dom σ) as Hfresh.
  repeat setoid_rewrite not_elem_of_union in Hfresh.
  split_and!.
  - rewrite /state_fresh -(location_add_0 (location_fresh _)) //.
    apply not_elem_of_dom, Hfresh => //.
  - rewrite /state_fresh -(location_add_0 (location_fresh _)) //.
    apply not_elem_of_dom, Hfresh => //.
  - intros i Hi.
    split_and!.
    all: apply not_elem_of_dom, Hfresh; lia.
Qed.

(** ** Physical equality *)

Implicit Types i : nat.

Variant lowliteral :=
  | LowlitInt n
  | LowlitLoc l
  | LowlitPoison.
Implicit Types llit : lowliteral.

#[global] Instance lowliteral_eq_dec : EqDecision lowliteral :=
  ltac:(solve_decision).

Definition literal_to_low lit :=
  match lit with
  | LitBool b =>
      LowlitInt (Nat.b2n b)
  | LitInt n =>
      LowlitInt n
  | LitLoc l =>
      LowlitLoc l
  | LitPoison =>
      LowlitPoison
  end.
#[global] Arguments literal_to_low !_ / : simpl nomatch, assert.

#[global] Instance lowliteral_nonsimilar : Nonsimilar lowliteral :=
  λ llit1 llit2,
    match llit1 with
    | LowlitInt n1 =>
        llit2 ≠ LowlitInt n1
    | LowlitLoc l1 =>
        llit2 ≠ LowlitLoc l1
    | _ =>
        True
    end.

#[global] Instance lowliteral_nonsimilar_dec :
  RelDecision (≉@{lowliteral}).
Proof.
  unshelve refine (
    λ llit1 llit2,
      match llit1 with
      | LowlitInt n1 =>
          decide (llit2 ≠ LowlitInt n1)
      | LowlitLoc l1 =>
          decide (llit2 ≠ LowlitLoc l1)
      | _ =>
          left _
      end
  ).
  all: abstract done.
Defined.

#[global] Instance lowliteral_nonsimilar_symmetric :
  Symmetric (≉@{lowliteral}).
Proof.
  intros [] []; done.
Qed.

Unset Elimination Schemes.
Inductive lowval :=
  | LowvalLit llit
  | LowvalRecs
  | LowvalBlock gen tag vs (lvs : list lowval).
Set Elimination Schemes.
Implicit Types lv : lowval.
Implicit Types lvs : list lowval.

Section lowval_ind.
  Variable P : lowval → Prop.

  Variable HLit :
    ∀ llit,
    P (LowvalLit llit).
  Variable HRecs :
    P LowvalRecs.
  Variable HBlock :
    ∀ gen tag vs,
    ∀ lvs, Forall P lvs →
    P (LowvalBlock gen tag vs lvs).

  Fixpoint lowval_ind lv :=
    match lv with
    | LowvalLit llit =>
        HLit
          llit
    | LowvalRecs =>
        HRecs
    | LowvalBlock gen tag vs lvs =>
        HBlock
          gen tag vs
          lvs (Forall_true P lvs lowval_ind)
    end.
End lowval_ind.

Notation LowvalInt n := (
  LowvalLit (LowlitInt n)
)(only parsing
).
Notation LowvalLoc l := (
  LowvalLit (LowlitLoc l)
)(only parsing
).
Notation LowvalPoison := (
  LowvalLit LowlitPoison
)(only parsing
).

#[global] Instance lowval_eq_dec : EqDecision lowval.
Proof.
  unshelve refine (
    fix go lv1 lv2 : Decision (lv1 = lv2) :=
      let fix go_list lvs1 lvs2 : Decision (lvs1 = lvs2) :=
        match lvs1, lvs2 with
        | [], [] =>
            left _
        | lv1 :: lvs1, lv2 :: lvs2 =>
            cast_if_and
              (decide (lv1 = lv2))
              (decide (lvs1 = lvs2))
        | _, _ =>
            right _
        end
      in
      match lv1, lv2 with
      | LowvalLit llit1, LowvalLit llit2 =>
          cast_if
            (decide (llit1 = llit2))
      | LowvalRecs, LowvalRecs =>
          left _
      | LowvalBlock gen1 tag1 vs1 lvs1, LowvalBlock gen2 tag2 vs2 lvs2 =>
          cast_if_and4
            (decide (gen1 = gen2))
            (decide (tag1 = tag2))
            (decide (vs1 = vs2))
            (decide (lvs1 = lvs2))
      | _, _ =>
          right _
      end
  ).
  all: abstract congruence.
Defined.

Fixpoint val_to_low v :=
  match v with
  | ValLit llit =>
      LowvalLit (literal_to_low llit)
  | ValRecs _ _ =>
      LowvalRecs
  | ValBlock _ tag [] =>
      LowvalLit (LowlitInt tag)
  | ValBlock gen tag vs =>
      LowvalBlock gen tag vs (val_to_low <$> vs)
  end.
#[global] Arguments val_to_low !_ / : simpl nomatch, assert.

#[global] Instance lowval_nonsimilar : Nonsimilar lowval :=
  λ lv1 lv2,
    match lv1 with
    | LowvalLit llit1 =>
        match lv2 with
        | LowvalLit llit2 =>
            llit1 ≉ llit2
        | _ =>
            True
        end
    | LowvalBlock (Generative (Some bid1)) tag1 vs1 _ =>
        match lv2 with
        | LowvalBlock (Generative (Some bid2)) tag2 vs2 _ =>
            bid1 ≠ bid2 ∨
            tag1 ≠ tag2 ∨
            vs1 ≠ vs2
        | _ =>
            True
        end
    | _ =>
        True
    end.

#[global] Instance lowval_nonsimilar_dec :
  RelDecision (≉@{lowval}).
Proof.
  unshelve refine (
    λ lv1 lv2,
      match lv1 with
      | LowvalLit llit1 =>
          match lv2 with
          | LowvalLit llit2 =>
              decide (llit1 ≉ llit2)
          | _ =>
              left _
          end
      | LowvalBlock (Generative (Some bid1)) tag1 vs1 _ =>
          match lv2 with
          | LowvalBlock (Generative (Some bid2)) tag2 vs2 _ =>
              cast_if_or3
                (decide (bid1 ≠ bid2))
                (decide (tag1 ≠ tag2))
                (decide (vs1 ≠ vs2))
          | _ =>
              left _
          end
      | _ =>
          left _
      end
  ).
  all: abstract naive_solver.
Defined.

#[global] Instance lowval_similar : Similar lowval :=
  fix go lv1 lv2 :=
    match lv1 with
    | LowvalLit llit1 =>
        lv2 = LowvalLit llit1
    | LowvalRecs =>
        lv2 = LowvalRecs
    | LowvalBlock gen1 tag1 vs1 lvs1 =>
        match lv2 with
        | LowvalBlock gen2 tag2 vs2 lvs2 =>
            match gen1, gen2 with
            | Generative bid1, Generative bid2 =>
                bid1 = bid2 ∧
                tag1 = tag2 ∧
                vs1 = vs2
            | Nongenerative, Nongenerative =>
                tag1 = tag2 ∧
                Forall2' go lvs1 lvs2
            | _, _ =>
                False
            end
        | _ =>
            False
        end
    end.

#[global] Instance lowval_similar_dec :
  RelDecision (≈@{lowval}).
Proof.
  refine (
    fix go lv1 lv2 :=
      match lv1 with
      | LowvalLit llit1 =>
          decide (lv2 = LowvalLit llit1)
      | LowvalRecs =>
          decide (lv2 = LowvalRecs)
      | LowvalBlock gen1 tag1 vs1 lvs1 =>
          match lv2 with
          | LowvalBlock gen2 tag2 vs2 lvs2 =>
              match gen1, gen2 with
              | Generative bid1, Generative bid2 =>
                  cast_if_and3
                    (decide (bid1 = bid2))
                    (decide (tag1 = tag2))
                    (decide (vs1 = vs2))
              | Nongenerative, Nongenerative =>
                  cast_if_and
                    (decide (tag1 = tag2))
                    (@decide (Forall2' (≈) lvs1 lvs2) (@Forall2'_dec _ _ _ go _ _))
              | _, _ =>
                  right _
              end
          | _ =>
              right _
          end
      end
  ).
  all: simpl.
  all: abstract intuition.
Defined.

#[global] Instance lowval_nonsimilar_symmetric :
  Symmetric (≉@{lowval}).
Proof.
  do 2 intros [| | [[] |]]; naive_solver.
Qed.

#[global] Instance lowval_similar_reflexive :
  Reflexive (≈@{lowval}).
Proof.
  rewrite /Reflexive. fix IH 1.
  intros [| | []].
  4: apply Forall2'_refl in IH as ?.
  all: clear IH.
  all: naive_solver.
Qed.
#[global] Instance lowval_similar_symmetric :
  Symmetric (≈@{lowval}).
Proof.
  rewrite /Symmetric. fix IH 1.
  do 2 intros [| | []].
  16: apply Forall2'_sym in IH as ?.
  all: clear IH.
  all: naive_solver.
Qed.
#[global] Instance lowval_similar_transitive :
  Transitive (≈@{lowval}).
Proof.
  rewrite /Transitive. fix IH 1.
  do 3 intros [| | []].
  64: apply Forall2'_trans in IH as ?.
  all: clear IH.
  all: naive_solver.
Qed.

Lemma lowval_similar_or_nonsimilar lv1 lv2 :
  lv1 ≈ lv2 ∨ lv1 ≉ lv2.
Proof.
  all: destruct lv1 as [[n1 | l1 |] | | [[bid1 |] |] tag1 [| v1 vs1]].
  all: destruct lv2 as [[n2 | l2 |] | | [[bid2 |] |] tag2 [| v2 vs2]].
  all: try destruct_decide (n1 = n2).
  all: try destruct_decide (l1 = l2).
  all: try destruct_decide (bid1 = bid2).
  all: try destruct_decide (tag1 = tag2).
  all: try destruct_decide (v1 = v2).
  all: try destruct_decide (vs1 = vs2).
  all: cbn; naive_solver.
Qed.
#[global] Instance val_nonsimilar : Nonsimilar val :=
  λ v1 v2,
    val_to_low v1 ≉ val_to_low v2.

#[global] Instance val_nonsimilar_dec : RelDecision (≉@{val}) :=
  ltac:(rewrite /nonsimilar /val_nonsimilar; solve_decision).

#[global] Instance val_similar : Similar val :=
  λ v1 v2,
    val_to_low v1 ≈ val_to_low v2.

#[global] Instance val_similar_dec : RelDecision (≈@{val}) :=
  ltac:(rewrite /similar /val_similar; solve_decision).

#[global] Instance val_nonsimilar_symmetric :
  Symmetric (≉@{val}).
Proof.
  rewrite /nonsimilar /val_nonsimilar /Symmetric //.
Qed.
Lemma val_nonsimilar_bool b1 b2 :
  ValBool b1 ≉ ValBool b2 →
  b1 ≠ b2.
Proof.
  naive_solver.
Qed.
Lemma val_nonsimilar_int n1 n2 :
  ValInt n1 ≉ ValInt n2 →
  n1 ≠ n2.
Proof.
  naive_solver.
Qed.
Lemma val_nonsimilar_nat (n1 n2 : nat) :
  ValNat n1 ≉ ValNat n2 →
  n1 ≠ n2.
Proof.
  naive_solver.
Qed.
Lemma val_nonsimilar_location l1 l2 :
  ValLoc l1 ≉ ValLoc l2 →
  l1 ≠ l2.
Proof.
  naive_solver.
Qed.
Lemma val_nonsimilar_block_empty gen1 tag1 gen2 tag2 :
  ValBlock gen1 tag1 [] ≉ ValBlock gen2 tag2 [] →
  tag1 ≠ tag2.
Proof.
  naive_solver.
Qed.
Lemma val_nonsimilar_block_generative bid1 tag1 vs1 bid2 tag2 vs2 :
  tag1 = tag2 →
  vs1 = vs2 →
  ValBlock (Generative (Some bid1)) tag1 vs1 ≉ ValBlock (Generative (Some bid2)) tag2 vs2 →
  length vs1 = 0 ∨ bid1 ≠ bid2.
Proof.
  intros <- <-.
  destruct vs1; first done.
  cbn. naive_solver.
Qed.

#[global] Instance val_similar_reflexive :
  Reflexive (≈@{val}).
Proof.
  rewrite /similar /val_similar /Reflexive //.
Qed.
Lemma val_similar_refl v1 v2 :
  v1 = v2 →
  v1 ≈ v2.
Proof.
  naive_solver.
Qed.
#[global] Instance val_similar_symmetric :
  Symmetric (≈@{val}).
Proof.
  rewrite /similar /val_similar /Symmetric //.
Qed.
#[global] Instance val_similar_transitive :
  Transitive (≈@{val}).
Proof.
  rewrite /similar /val_similar /Transitive.
  firstorder. etrans; done.
Qed.
Lemma val_similar_bool b1 b2 :
  ValLit (LitBool b1) ≈ ValLit (LitBool b2) →
  b1 = b2.
Proof.
  intros [= ->%(inj _)%(inj _)]. done.
Qed.
Lemma val_similar_int n1 n2 :
  ValLit (LitInt n1) ≈ ValLit (LitInt n2) →
  n1 = n2.
Proof.
  intros [= ->]. done.
Qed.
Lemma val_similar_nat (n1 n2 : nat) :
  ValLit (LitInt n1) ≈ ValLit (LitInt n2) →
  n1 = n2.
Proof.
  intros <-%val_similar_int%(inj _). done.
Qed.
Lemma val_similar_location l1 l2 :
  ValLit (LitLoc l1) ≈ ValLit (LitLoc l2) →
  l1 = l2.
Proof.
  intros [= ->]. done.
Qed.
Lemma val_similar_block_empty gen1 tag1 gen2 tag2 :
  ValBlock gen1 tag1 [] ≈ ValBlock gen2 tag2 [] →
  tag1 = tag2.
Proof.
  intros [= ->%(inj _)]. done.
Qed.
Lemma val_similar_block_empty_1 gen1 tag1 gen2 tag2 v2 vs2 :
  ¬ ValBlock gen1 tag1 [] ≈ ValBlock gen2 tag2 (v2 :: vs2).
Proof.
  done.
Qed.
Lemma val_similar_block_empty_2 gen1 tag1 v1 vs1 gen2 tag2 :
  ¬ ValBlock gen1 tag1 (v1 :: vs1) ≈ ValBlock gen2 tag2 [].
Proof.
  intros []%symmetry%val_similar_block_empty_1.
Qed.
Lemma val_similar_block_generative bid1 tag1 vs1 bid2 tag2 vs2 :
  length vs1 ≠ 0 ∨ length vs2 ≠ 0 →
  ValBlock (Generative bid1) tag1 vs1 ≈ ValBlock (Generative bid2) tag2 vs2 →
    bid1 = bid2 ∧
    tag1 = tag2 ∧
    vs1 = vs2.
Proof.
  destruct vs1, vs2; naive_solver.
Qed.
Lemma val_similar_block_nongenerative tag1 vs1 tag2 vs2 :
  ValBlock Nongenerative tag1 vs1 ≈ ValBlock Nongenerative tag2 vs2 →
    tag1 = tag2 ∧
    length vs1 = length vs2.
Proof.
  destruct vs1, vs2; try done.
  - intros [= ->%(inj _)]. done.
  - intros (<- & Hlen%Forall2'_length).
    simpl_length in Hlen.
Qed.
Lemma val_similar_location_block l gen tag vs :
  ¬ ValLit (LitLoc l) ≈ ValBlock gen tag vs.
Proof.
  destruct vs; done.
Qed.
Lemma val_similar_block_location gen tag vs l :
  ¬ ValBlock gen tag vs ≈ ValLit (LitLoc l).
Proof.
  intros []%symmetry%val_similar_location_block.
Qed.
Lemma val_similar_block_generative_nongenerative bid1 tag1 vs1 tag2 vs2 :
  length vs1 ≠ 0 ∨ length vs2 ≠ 0 →
  ¬ ValBlock (Generative bid1) tag1 vs1 ≈ ValBlock Nongenerative tag2 vs2.
Proof.
  destruct vs1, vs2; cbn; naive_solver lia.
Qed.
Lemma val_similar_block_nongenerative_generative tag1 vs1 bid2 tag2 vs2 :
  length vs1 ≠ 0 ∨ length vs2 ≠ 0 →
  ¬ ValBlock Nongenerative tag1 vs1 ≈ ValBlock (Generative bid2) tag2 vs2.
Proof.
  intros ? []%symmetry%val_similar_block_generative_nongenerative. naive_solver.
Qed.

Lemma val_similar_or_nonsimilar v1 v2 :
  v1 ≈ v2 ∨ v1 ≉ v2.
Proof.
  apply lowval_similar_or_nonsimilar.
Qed.
Definition in_type (_ : string) (n : nat) :=
  n.
#[global] Arguments in_type : simpl never.

Coercion LitBool : bool >-> literal.
Coercion LitInt : Z >-> literal.
Coercion LitLoc : location >-> literal.

Coercion Val : val >-> expr.
Coercion Var : string >-> expr.
Coercion App : expr >-> Funclass.

Declare Custom Entry mizzle_rec.
Declare Scope mizzle_recs_scope.
Delimit Scope mizzle_recs_scope with mizzle_recs.

Declare Custom Entry mizzle_field.
Declare Custom Entry mizzle_tag.
Declare Custom Entry mizzle_proj.
Declare Custom Entry mizzle_branch.

Number Notation
  val
  val_of_int
  val_to_int
: expr_scope.
Number Notation
  val
  val_of_int
  val_to_int
: val_scope.

Notation "'true'" := (
  Corelib.Init.Datatypes.true
) : core_scope.
Notation "'true'" := (
  Val (ValLit (LitBool true))
) : expr_scope.
Notation "'true'" := (
  ValLit (LitBool true)
) : val_scope.

Notation "'false'" := (
  Corelib.Init.Datatypes.false
) : core_scope.
Notation "'false'" := (
  Val (ValLit (LitBool false))
) : expr_scope.
Notation "'false'" := (
  ValLit (LitBool false)
) : val_scope.

Notation "0" :=
  0
( in custom mizzle_field
).
Notation "1" :=
  1
( in custom mizzle_field
).
Notation "2" :=
  2
( in custom mizzle_field
).
Notation "3" :=
  3
( in custom mizzle_field
).
Notation "4" :=
  4
( in custom mizzle_field
).
Notation "5" :=
  5
( in custom mizzle_field
).
Notation "6" :=
  6
( in custom mizzle_field
).
Notation "7" :=
  7
( in custom mizzle_field
).
Notation "8" :=
  8
( in custom mizzle_field
).
Notation "9" :=
  9
( in custom mizzle_field
).

Notation "0" :=
  0
( in custom mizzle_tag
).

Notation "0" :=
  0
( in custom mizzle_proj
).
Notation "1" :=
  1
( in custom mizzle_proj
).
Notation "2" :=
  2
( in custom mizzle_proj
).
Notation "3" :=
  3
( in custom mizzle_proj
).
Notation "4" :=
  4
( in custom mizzle_proj
).
Notation "5" :=
  5
( in custom mizzle_proj
).
Notation "6" :=
  6
( in custom mizzle_proj
).
Notation "7" :=
  7
( in custom mizzle_proj
).
Notation "8" :=
  8
( in custom mizzle_proj
).
Notation "9" :=
  9
( in custom mizzle_proj
).

Notation "# l" := (
  ValLit l%Z%V%stdpp
)(at level 8,
  format "# l"
).
Notation "'#@{' X }" := (
  λ x : X, ValLit x
)(only parsing
).
Notation "'#*@{' X }" := (
  @fmap _ _ X val (λ x : X, ValLit x)
)(only parsing
).

Notation "f x => e" := (
  @pair (prod binder binder) expr
    (@pair binder binder f%binder x%binder)
    e%E
)(in custom mizzle_rec at level 200,
  f constr at level 1,
  x constr at level 1,
  e constr at level 200,
  format "f  x  =>  '/  ' '[' e ']'"
).
Notation "f x0 x1 .. xn => e" := (
  @pair (prod binder binder) expr
    (@pair binder binder f%binder x0%binder)
    (Fun x1%binder .. (Fun xn%binder e%E) ..)
)(in custom mizzle_rec at level 200,
  f constr at level 1,
  x0 constr at level 1,
  x1 constr at level 1,
  xn constr at level 1,
  e constr at level 200,
  format "f  x0  x1  ..  xn  =>  '/  ' '[' e ']'"
).
Notation "'recs:' rec1 'and:' .. 'and:' recn" := (
  @cons recursive rec1 (.. (@cons recursive recn (@nil recursive)) ..)
)(at level 200,
  rec1 custom mizzle_rec,
  recn custom mizzle_rec,
  format "'[v' recs:  rec1 '/' and:  .. '/' and:  recn ']'"
) : mizzle_recs_scope.

Notation "'rec:' f x => e" := (
  Rec f%binder x%binder e%E
)(at level 200,
  f, x at level 1,
  e at level 200,
  format "'[hv' 'rec:'  f  x  =>  '/  ' '[' e ']' ']'"
) : expr_scope.
Notation "'vrec:' f x => e" := (
  ValRec f%binder x%binder e%E
)(at level 200,
  f, x at level 1,
  e at level 200,
  format "'[hv' 'vrec:'  f  x  =>  '/  ' '[' e ']' ']'"
) : val_scope.
Notation "'rec:' f x0 x1 .. xn => e" := (
  Rec f%binder x0%binder (Fun x1%binder .. (Fun xn%binder e%E) ..)
)(at level 200,
  f, x0, x1, xn at level 1,
  e at level 200,
  format "'[hv' 'rec:'  f  x0  x1  ..  xn  =>  '/  ' '[' e ']' ']'"
) : expr_scope.
Notation "'vrec:' f x0 x1 .. xn => e" := (
  ValRec f%binder x0%binder (Fun x1%binder .. (Fun xn%binder e%E) ..)
)(at level 200,
  f, x0, x1, xn at level 1,
  e at level 200,
  format "'[hv' 'vrec:'  f  x0  x1  ..  xn  =>  '/  ' '[' e ']' ']'"
) : val_scope.

(** Closures: [fun:]/[rec:] build an *expression* ([Fun]/[Rec]), which steps
    to the *value* written and printed [vfun:]/[vrec:] ([ValFun]/[ValRec]).
    The two spellings keep a goal honest about which one it holds.
    (Mizzle divergence from Zoo, where both were [fun:].) *)
Notation "'fun:' x => e" := (
  Fun x%binder e%E
)(at level 200,
  x at level 1,
  e at level 200,
  format "'[hv' 'fun:'  x  =>  '/  ' '[' e ']' ']'"
) : expr_scope.
Notation "'fun:' x0 x1 .. xn => e" := (
  Fun x0%binder (Fun x1%binder .. (Fun xn%binder e%E) ..)
)(at level 200,
  x0, x1, xn at level 1,
  e at level 200,
  format "'[hv' 'fun:'  x0  x1  ..  xn  =>  '/  ' '[' e ']' ']'"
) : expr_scope.
Notation "'vfun:' x => e" := (
  ValFun x%binder e%E
)(at level 200,
  x at level 1,
  e at level 200,
  format "'[hv' 'vfun:'  x  =>  '/  ' '[' e ']' ']'"
) : val_scope.
Notation "'vfun:' x0 x1 .. xn => e" := (
  ValFun x0%binder (Fun x1%binder .. (Fun xn%binder e%E) .. )
)(at level 200,
  x0, x1, xn at level 1,
  e at level 200,
  format "'[hv' 'vfun:'  x0  x1  ..  xn  =>  '/  ' '[' e ']' ']'"
) : val_scope.

Notation "'letrec:' f x := e1 'in' e2" := (
  Let f%binder (Rec f%binder x%binder e1%E) e2%E
)(at level 200,
  f, x at level 1,
  e1, e2 at level 200,
  format "'[v' '[hv' 'letrec:'  f  x  :=  '/  ' '[' e1 ']'  '/' 'in'  ']' '/' e2 ']'"
) : expr_scope.
Notation "'letrec:' f x0 x1 .. xn := e1 'in' e2" := (
  Let f%binder (Rec f%binder x0%binder (Fun x1%binder .. (Fun xn%binder e1%E) ..)) e2%E
)(at level 200,
  f, x0, x1, xn at level 1,
  e1, e2 at level 200,
  format "'[v' '[hv' 'letrec:'  f  x0  x1  ..  xn  :=  '/  ' '[' e1 ']'  '/' 'in'  ']' '/' e2 ']'"
) : expr_scope.

Notation "'let:' x := e1 'in' e2" := (
  Let x%binder e1%E e2%E
)(at level 200,
  x at level 1,
  e1, e2 at level 200,
  format "'[v' '[hv' 'let:'  x  :=  '/  ' '[' e1 ']'  '/' 'in'  ']' '/' e2 ']'"
) : expr_scope.
Notation "'let:' f x := e1 'in' e2" := (
  Let f%binder (Fun x%binder e1%E) e2%E
)(at level 200,
  f, x at level 1,
  e1, e2 at level 200,
  format "'[v' '[hv' 'let:'  f  x  :=  '/  ' '[' e1 ']'  '/' 'in'  ']' '/' e2 ']'"
) : expr_scope.
Notation "'let:' f x0 x1 .. xn := e1 'in' e2" := (
  Let f%binder (Fun x0%binder (Fun x1%binder .. (Fun xn%binder e1%E) ..)) e2%E
)(at level 200,
  f, x0, x1, xn at level 1,
  e1, e2 at level 200,
  format "'[v' '[hv' 'let:'  f  x0  x1  ..  xn  :=  '/  ' '[' e1 ']'  '/' 'in'  ']' '/' e2 ']'"
) : expr_scope.

Notation "e1 ;; e2" := (
  Let BAnon e1%E e2%E
)(at level 100,
  e2 at level 200,
  format "'[v' '[' e1 ']'  ;;  '/' e2 ']'"
) : expr_scope.

Notation "~ e" := (
  Unop UnopNeg e%E
)(at level 75,
  right associativity
) : expr_scope.
Notation "- e" := (
  Unop UnopMinus e%E
)(at level 35,
  right associativity
) : expr_scope.

Notation "e1 + e2" := (
  Binop BinopPlus e1%E e2%E
)(at level 50,
  left associativity
) : expr_scope.
Notation "e1 - e2" := (
  Binop BinopMinus e1%E e2%E
)(at level 50,
  left associativity
) : expr_scope.
Notation "e1 * e2" := (
  Binop BinopMult e1%E e2%E
)(at level 40,
  left associativity
) : expr_scope.
(* Level 35 binds *tighter* than [*] at 40, so [a * b `quot` c] parses as
   [a * (b `quot` c)] -- the opposite grouping to OCaml, where [/] and [mod]
   share the precedence of [*] and associate left. The level is not ours to
   pick: stdpp already takes these two tokens at level 35 in [Z_scope]
   ([stdpp/numbers.v]), and Rocq fixes a notation string's level globally,
   across scopes. Vendoring the language does not change that.
   [ocaml2mizzle] compensates by always parenthesizing a [`quot`]/[`rem`]
   operand, so its output reads the way it parses. *)
Notation "e1 `quot` e2" := (
  Binop BinopQuot e1%E e2%E
)(at level 35
) : expr_scope.
Notation "e1 `rem` e2" := (
  Binop BinopRem e1%E e2%E
)(at level 35
) : expr_scope.
Notation "e1 `land` e2" := (
  Binop BinopLand e1%E e2%E
)(at level 31,
  left associativity
) : expr_scope.
Notation "e1 `lor` e2" := (
  Binop BinopLor e1%E e2%E
)(at level 32,
  left associativity
) : expr_scope.
Notation "e1 `lsl` e2" := (
  Binop BinopLsl e1%E e2%E
)(at level 30,
  right associativity
) : expr_scope.
Notation "e1 `lsr` e2" := (
  Binop BinopLsr e1%E e2%E
)(at level 30,
  right associativity
) : expr_scope.
Notation "e1 ≤ e2" := (
  Binop BinopLe e1%E e2%E
)(at level 70,
  no associativity
) : expr_scope.
Notation "e1 < e2" := (
  Binop BinopLt e1%E e2%E
)(at level 70,
  no associativity
) : expr_scope.
Notation "e1 ≥ e2" := (
  Binop BinopGe e1%E e2%E
)(at level 70,
  no associativity
) : expr_scope.
Notation "e1 > e2" := (
  Binop BinopGt e1%E e2%E
)(at level 70,
  no associativity
) : expr_scope.
Notation "e1 == e2" := (
  Equal e1%E e2%E
)(at level 70,
  no associativity
) : expr_scope.
Notation "e1 != e2" := (
  Unop UnopNeg (Equal e1%E e2%E)
)(at level 70,
  no associativity
) : expr_scope.
Notation "e1 'and' e2" := (
  If e1%E e2%E (ValBool false)
)(at level 76,
  left associativity,
  only parsing
) : expr_scope.
Notation "e1 'or' e2" := (
  If e1%E (ValBool true) e2%E
)(at level 77,
  left associativity,
  only parsing
) : expr_scope.

Notation "'if:' e0 'then' e1 'else' e2" := (
  If e0%E e1%E e2%E
)(at level 1,
  e0, e1 at level 200,
  e2 at level 1,
  only parsing
) : expr_scope.
Notation "'if:' e0 'then' ( e1 ) 'else' ( e2 )" := (
  If e0%E e1%E e2%E
)(at level 1,
  e0, e1, e2 at level 200,
  only printing,
  format "'[v' '[hv' if:  '/  ' '[' e0 ']'  '/' then  ( ']' '/  ' '[' e1 ']' '/' )  else  ( '/  ' '[' e2 ']' '/' ) ']'"
) : expr_scope.
Notation "'if:' e0 'then' e1" := (
  If e0%E e1%E Unit
)(at level 1,
  e0, e1 at level 200,
  only parsing
) : expr_scope.

Notation "'while:' e0 'begin' e1 'end'" := (
  While e0%E e1%E
)(e0, e1 at level 200,
  format "'[v' '[hv' while:  '/  ' '[' e0 ']'  '/' begin  ']' '/  ' '[' e1 ']'  '/' end ']'"
) : expr_scope.

Notation "'for:' x := e1 'to' e2 'begin' e3 'end'" := (
  For e1%E e2%E (Fun x%binder e3%E)
)(x at level 1,
  e1, e2, e3 at level 200,
  format "'[v' '[hv' for:  x  :=  '/  ' '[' e1 ']'  '/' to  '/  ' '[' e2 ']'  '/' begin  ']' '/  ' '[' e3 ']'  '/' end ']'"
) : expr_scope.

Notation "{ e1 , .. , en }" := (
  Block Mutable 0 (@cons expr e1%E .. (@cons expr en%E (@nil expr)) ..)
)(e1, en at level 200,
  format "'[hv' {  '[' e1 ']' '/' ,  .. '/' ,  '[' en ']'  '/' } ']'"
) : expr_scope.

Notation "‘ tag { e1 , .. , en }" := (
  Block Mutable tag%core (@cons expr e1%E .. (@cons expr en%E (@nil expr)) ..)
)(at level 2,
  tag custom mizzle_tag,
  e1, en at level 200,
  format "'[hv' ‘ tag {  '/  ' '[' e1 ']' '/' ,  .. '/' ,  '[' en ']'  '/' } ']'"
) : expr_scope.

Notation "§ tag" := (
  tag
)(at level 2,
  tag custom mizzle_tag,
  format "§ tag"
) : stdpp_scope.
Notation "§ tag" := (
  Val (ValBlock Nongenerative tag%core (@nil val))
)(at level 2,
  tag custom mizzle_tag,
  format "§ tag"
) : expr_scope.
Notation "§ tag" := (
  ValBlock Nongenerative tag%core (@nil val)
)(at level 2,
  tag custom mizzle_tag,
  format "§ tag"
) : val_scope.

Notation "‘ tag ( e1 , .. , en )" := (
  Block ImmutableNongenerative tag%core (@cons expr e1%E .. (@cons expr en%E (@nil expr)) ..)
)(at level 2,
  tag custom mizzle_tag,
  e1, en at level 200,
  format "'[hv' ‘ tag (  '/  ' '[' e1 ']' '/' ,  .. '/' ,  '[' en ']'  '/' ) ']'"
) : expr_scope.
Notation "’ tag ( v1 , .. , vn )" := (
  Val (ValBlock Nongenerative tag%core (@cons val v1%V .. (@cons val vn%V (@nil val)) ..))
)(at level 2,
  tag custom mizzle_tag,
  v1, vn at level 200,
  format "'[hv' ’ tag (  '/  ' '[' v1 ']' '/' ,  .. '/' ,  '[' vn ']'  '/' ) ']'"
): expr_scope.
Notation "‘ tag ( v1 , .. , vn )" := (
  ValBlock Nongenerative tag%core (@cons val v1%V .. (@cons val vn%V (@nil val)) ..)
)(at level 2,
  tag custom mizzle_tag,
  v1, vn at level 200,
  format "'[hv' ‘ tag (  '/  ' '[' v1 ']' '/' ,  .. '/' ,  '[' vn ']'  '/' ) ']'"
): val_scope.
(** The two quotes distinguish an *expression* from a *value*: in
    [expr_scope], [‘tag(e…)] is a [Block] that still has to reduce, while
    [’tag(v…)] is already a [Val].  In [val_scope] that distinction is
    vacuous — everything there is a value — so both glyphs mean the same
    thing, and the [’] spellings below exist so that choosing the wrong
    curl is not a parse error.  Parsing only: printing stays on [‘]. *)

Notation "’ tag ( v1 , .. , vn )" := (
  ValBlock Nongenerative tag%core (@cons val v1%V .. (@cons val vn%V (@nil val)) ..)
)(at level 2,
  tag custom mizzle_tag,
  v1, vn at level 200,
  only parsing
): val_scope.

Notation "‘ tag [ e1 , .. , en ]" := (
  Block ImmutableGenerativeWeak tag%core (@cons expr e1%E .. (@cons expr en%E (@nil expr)) ..)
)(at level 2,
  tag custom mizzle_tag,
  e1, en at level 200,
  format "'[hv' ‘ tag [  '/  ' '[' e1 ']' '/' ,  .. '/' ,  '[' en ']'  '/' ] ']'"
) : expr_scope.
Notation "’ tag [ v1 , .. , vn ]" := (
  Val (ValBlock (Generative None) tag%core (@cons val v1%V .. (@cons val vn%V (@nil val)) ..))
)(at level 2,
  tag custom mizzle_tag,
  v1, vn at level 200,
  format "'[hv' ’ tag [  '/  ' '[' v1 ']' '/' ,  .. '/' ,  '[' vn ']'  '/' ] ']'"
): expr_scope.
Notation "‘ tag [ v1 , .. , vn ]" := (
  ValBlock (Generative None) tag%core (@cons val v1%V .. (@cons val vn%V (@nil val)) ..)
)(at level 2,
  tag custom mizzle_tag,
  v1, vn at level 200,
  format "'[hv' ‘ tag [  '/  ' '[' v1 ']' '/' ,  .. '/' ,  '[' vn ']'  '/' ] ']'"
): val_scope.
Notation "’ tag [ v1 , .. , vn ]" := (
  ValBlock (Generative None) tag%core (@cons val v1%V .. (@cons val vn%V (@nil val)) ..)
)(at level 2,
  tag custom mizzle_tag,
  v1, vn at level 200,
  only parsing
): val_scope.

Notation "‘ tag '@[' e1 , .. , en ]" := (
  Block ImmutableGenerativeStrong tag%core (@cons expr e1%E .. (@cons expr en%E (@nil expr)) ..)
)(at level 2,
  tag custom mizzle_tag,
  e1, en at level 200,
  format "'[hv' ‘ tag @[  '/  ' '[' e1 ']' '/' ,  .. '/' ,  '[' en ']'  '/' ] ']'"
) : expr_scope.
Notation "’ tag @ bid [ v1 , .. , vn ]" := (
  Val (ValBlock (Generative (Some bid)) tag%core (@cons val v1%V .. (@cons val vn%V (@nil val)) ..))
)(at level 2,
  tag custom mizzle_tag,
  bid at level 1,
  v1, vn at level 200,
  format "'[hv' ’ tag @ bid [  '/  ' '[' v1 ']' '/' ,  .. '/' ,  '[' vn ']'  '/' ] ']'"
): expr_scope.
Notation "‘ tag @ bid [ v1 , .. , vn ]" := (
  ValBlock (Generative (Some bid)) tag%core (@cons val v1%V .. (@cons val vn%V (@nil val)) ..)
)(at level 2,
  tag custom mizzle_tag,
  bid at level 1,
  v1, vn at level 200,
  format "'[hv' ‘ tag @ bid [  '/  ' '[' v1 ']' '/' ,  .. '/' ,  '[' vn ']'  '/' ] ']'"
): val_scope.
Notation "’ tag @ bid [ v1 , .. , vn ]" := (
  ValBlock (Generative (Some bid)) tag%core (@cons val v1%V .. (@cons val vn%V (@nil val)) ..)
)(at level 2,
  tag custom mizzle_tag,
  bid at level 1,
  v1, vn at level 200,
  only parsing
): val_scope.

Notation "( v1 , v2 , .. , vn )" := (
  Val (ValBlock Nongenerative 0 (@cons val v1%V (@cons val v2%V .. (@cons val vn%V (@nil val)) ..)))
)(at level 0,
  only printing
) : expr_scope.
Notation "( e1 , e2 , .. , en )" := (
  Block ImmutableNongenerative 0 (@cons expr e1%E (@cons expr e2%E .. (@cons expr en%E (@nil expr)) ..))
)(at level 0
) : expr_scope.
Notation "( v1 , v2 , .. , vn )" := (
  ValBlock Nongenerative 0 (@cons val v1%V (@cons val v2%V .. (@cons val vn%V (@nil val)) ..))
)(at level 0
) : val_scope.
Notation "()" := (
  Unit
) : expr_scope.
Notation "()" :=
  ValUnit
: val_scope.

Notation "[ ] => e" := (
  @pair pattern expr
    ( Build_pattern
        (in_type "@list" 0)
        (@nil binder)
        BAnon
    )
    e%E
)(in custom mizzle_branch at level 200,
  e constr at level 200,
  format "[ ]  =>  '/    ' '[' e ']'"
).
Notation "[ ] 'as' x => e" := (
  @pair pattern expr
    ( Build_pattern
        (in_type "@list" 0)
        (@nil binder)
        (BNamed x%string)
    )
    e%E
)(in custom mizzle_branch at level 200,
  x constr at level 1,
  e constr at level 200,
  format "[ ]  as  x  =>  '/    ' '[' e ']'"
).
Notation "x1 :: x2 => e" := (
  @pair pattern expr
    ( Build_pattern
        (in_type "@list" 1)
        (@cons binder x1%binder (@cons binder x2%binder (@nil binder)))
        BAnon
    )
    e%E
)(in custom mizzle_branch at level 200,
  x1 constr at level 1,
  x2 constr at level 1,
  e constr at level 200,
  format "x1  ::  x2  =>  '/    ' '[' e ']'"
).
Notation "x1 :: x2 'as' y => e" := (
  @pair pattern expr
    ( Build_pattern
        (in_type "@list" 1)
        (@cons binder x1%binder (@cons binder x2%binder (@nil binder)))
        (BNamed y%string)
    )
    e%E
)(in custom mizzle_branch at level 200,
  x1 constr at level 1,
  x2 constr at level 1,
  y constr at level 1,
  e constr at level 200,
  format "x1  ::  x2  as  y  =>  '/    ' '[' e ']'"
).
Notation "tag => e" := (
  @pair pattern expr
    ( Build_pattern
        tag%core
        (@nil binder)
        BAnon
    )
    e%E
)(in custom mizzle_branch at level 200,
  tag custom mizzle_tag,
  e constr at level 200,
  format "tag  =>  '/    ' '[' e ']'"
).
Notation "tag 'as' x => e" := (
  @pair pattern expr
    ( Build_pattern
        tag%core
        (@nil binder)
        (BNamed x%string)
    )
    e%E
)(in custom mizzle_branch at level 200,
  tag custom mizzle_tag,
  x constr at level 1,
  e constr at level 200,
  format "tag  as  x  =>  '/    ' '[' e ']'"
).
Notation "tag 'as:' x => e" := (
  @pair pattern expr
    ( Build_pattern
        tag%core
        (@nil binder)
        x%binder
    )
    e%E
)(in custom mizzle_branch at level 200,
  tag custom mizzle_tag,
  x constr at level 1,
  e constr at level 200,
  format "tag  as:  x  =>  '/    ' '[' e ']'"
).
Notation "tag x1 .. xn => e" := (
  @pair pattern expr
    ( Build_pattern
        tag%core
        (@cons binder x1%binder .. (@cons binder xn%binder (@nil binder)) ..)
        BAnon
    )
    e%E
)(in custom mizzle_branch at level 200,
  tag custom mizzle_tag,
  x1 constr at level 1,
  xn constr at level 1,
  e constr at level 200,
  format "tag  x1  ..  xn  =>  '/    ' '[' e ']'"
).
Notation "tag x1 .. xn 'as' y => e" := (
  @pair pattern expr
    ( Build_pattern
        tag%core
        (@cons binder x1%binder .. (@cons binder xn%binder (@nil binder)) ..)
        (BNamed y%string)
    )
    e%E
)(in custom mizzle_branch at level 200,
  tag custom mizzle_tag,
  x1 constr at level 1,
  xn constr at level 1,
  y constr at level 1,
  e constr at level 200,
  format "tag  x1  ..  xn  as  y  =>  '/    ' '[' e ']'"
).
Notation "tag x1 .. xn 'as:' y => e" := (
  @pair pattern expr
    ( Build_pattern
        tag%core
        (@cons binder x1%binder .. (@cons binder xn%binder (@nil binder)) ..)
        y%binder
    )
    e%E
)(in custom mizzle_branch at level 200,
  tag custom mizzle_tag,
  x1 constr at level 1,
  xn constr at level 1,
  y constr at level 1,
  e constr at level 200,
  format "tag  x1  ..  xn  as:  y  =>  '/    ' '[' e ']'"
).

Notation "'match:' e 'with' | br_1 | .. | br_n 'end'" := (
  Match
    e%E
    BAnon
    Fail
    (@cons branch br_1 (.. (@cons branch br_n (@nil branch)) ..))
)(e at level 200,
  br_1 custom mizzle_branch at level 200,
  br_n custom mizzle_branch at level 200,
  format "'[v' '[hv' match:  '/  ' '[' e ']'  '/' with  ']' '/' |  br_1  '/' |  ..  '/' |  br_n  '/' end ']'"
) : expr_scope.
Notation "'match:' e 'with' br_1 | .. | br_n 'end'" := (
  Match
    e%E
    BAnon
    Fail
    (@cons branch br_1 (.. (@cons branch br_n (@nil branch)) ..))
)(e at level 200,
  br_1 custom mizzle_branch at level 200,
  br_n custom mizzle_branch at level 200,
  only parsing
) : expr_scope.
Notation "'match:' e0 'with' | br_1 | .. | br_n |_ => e1 'end'" := (
  Match
    e0%E
    BAnon
    e1%E
    (@cons branch br_1 (.. (@cons branch br_n (@nil branch)) ..))
)(e0, e1 at level 200,
  br_1 custom mizzle_branch at level 200,
  br_n custom mizzle_branch at level 200,
  format "'[v' '[hv' match:  '/  ' '[' e0 ']'  '/' with  ']' '/' |  br_1  '/' |  ..  '/' |  br_n  '/' |_  =>  '/    ' '[' e1 ']'  '/' end ']'"
) : expr_scope.
Notation "'match:' e0 'with' br_1 | .. | br_n |_ => e1 'end'" := (
  Match
    e0%E
    BAnon
    e1%E
    (@cons branch br_1 (.. (@cons branch br_n (@nil branch)) ..))
)(e0, e1 at level 200,
  br_1 custom mizzle_branch at level 200,
  br_n custom mizzle_branch at level 200,
  only parsing
) : expr_scope.
Notation "'match:' e0 'with' | br_1 | .. | br_n |_ 'as' x => e1 'end'" := (
  Match
    e0%E
    (BNamed x%string)
    e1%E
    (@cons branch br_1 (.. (@cons branch br_n (@nil branch)) ..))
)(e0, e1 at level 200,
  br_1 custom mizzle_branch at level 200,
  br_n custom mizzle_branch at level 200,
  x at level 1,
  format "'[v' '[hv' match:  '/  ' '[' e0 ']'  '/' with  ']' '/' |  br_1  '/' |  ..  '/' |  br_n  '/' |_  as  x  =>  '/    ' '[' e1 ']'  '/' end ']'"
) : expr_scope.
Notation "'match:' e0 'with' br_1 | .. | br_n |_ 'as' x => e1 'end'" := (
  Match
    e0%E
    (BNamed x%string)
    e1%E
    (@cons branch br_1 (.. (@cons branch br_n (@nil branch)) ..))
)(e0, e1 at level 200,
  br_1 custom mizzle_branch at level 200,
  br_n custom mizzle_branch at level 200,
  x at level 1,
  only parsing
) : expr_scope.
Notation "'match:' e0 'with' | br_1 | .. | br_n |_ 'as:' x => e1 'end'" := (
  Match
    e0%E
    x%binder
    e1%E
    (@cons branch br_1 (.. (@cons branch br_n (@nil branch)) ..))
)(e0, e1 at level 200,
  br_1 custom mizzle_branch at level 200,
  br_n custom mizzle_branch at level 200,
  x at level 1,
  format "'[v' '[hv' match:  '/  ' '[' e0 ']'  '/' with  ']' '/' |  br_1  '/' |  ..  '/' |  br_n  '/' |_  as:  x  =>  '/    ' '[' e1 ']'  '/' end ']'"
) : expr_scope.
Notation "'match:' e0 'with' br_1 | .. | br_n |_ 'as:' x => e1 'end'" := (
  Match
    e0%E
    x%binder
    e1%E
    (@cons branch br_1 (.. (@cons branch br_n (@nil branch)) ..))
)(e0, e1 at level 200,
  br_1 custom mizzle_branch at level 200,
  br_n custom mizzle_branch at level 200,
  x at level 1,
  only parsing
) : expr_scope.

Notation "'let:' ‘ tag x1 .. xn := e1 'in' e2" := (
  Match
    e1%E
    BAnon
    Fail
    ( @cons branch
        ( @pair pattern expr
            ( Build_pattern
                tag%core
                (@cons binder x1%binder .. (@cons binder xn%binder (@nil binder)) ..)
                BAnon
            )
            e2%E
        )
        (@nil branch)
    )
)(at level 200,
  tag custom mizzle_tag,
  x1, xn at level 1,
  e1, e2 at level 200,
  format "'[v' '[hv' 'let:'  ‘ tag  x1  ..  xn  :=  '/  ' '[' e1 ']'  '/' 'in'  ']' '/' e2 ']'"
) : expr_scope.
Notation "'let:' x0 , x1 , .. , xn := e1 'in' e2" := (
  Match
    e1%E
    BAnon
    Fail
    ( @cons branch
        ( @pair pattern expr
            ( Build_pattern
                0
                (@cons binder x0%binder (@cons binder x1%binder .. (@cons binder xn%binder (@nil binder)) ..))
                BAnon
            )
            e2%E
        )
        (@nil branch)
    )
)(at level 200,
  x0, x1, xn at level 1,
  e1, e2 at level 200,
  format "'[v' '[hv' 'let:'  x0 ,  x1 ,  .. ,  xn  :=  '/  ' '[' e1 ']'  '/' 'in'  ']' '/' e2 ']'"
) : expr_scope.

Notation "e .{ fld }" := (
  GetField NotAtomic e%E (Val (ValInt (Z.of_nat fld)))
)(at level 2,
  fld custom mizzle_field,
  left associativity,
  format "e .{ fld }"
) : expr_scope.

Notation "e .{ fld }ᵃᵗ" := (
  GetField Atomic e%E (Val (ValInt (Z.of_nat fld)))
)(at level 2,
  fld custom mizzle_field,
  left associativity,
  format "e .{ fld }ᵃᵗ"
) : expr_scope.

Notation "e .< proj >" := (
  GetField NotAtomic e%E (Val (ValInt (Z.of_nat proj)))
)(at level 2,
  proj custom mizzle_proj,
  format "e .< proj >"
) : expr_scope.

Notation "e1 <-{ fld }ᵃᵗ e2" := (
  SetField Atomic e1%E (Val (ValInt (Z.of_nat fld))) e2%E
)(at level 80,
  fld custom mizzle_field,
  format "'[hv' '[hv' '[' e1 ']'  '/  ' <-{ fld }ᵃᵗ  ']' '/  ' '[' e2 ']' ']'"
) : expr_scope.

Notation "e1 <-{ fld } e2" := (
  SetField NotAtomic e1%E (Val (ValInt (Z.of_nat fld))) e2%E
)(at level 80,
  fld custom mizzle_field,
  format "'[hv' '[hv' '[' e1 ']'  '/  ' <-{ fld }  ']' '/  ' '[' e2 ']' ']'"
) : expr_scope.

Notation "l .[ fld ]" := (
  location_add l (Z.of_nat fld)
)(at level 2,
  fld custom mizzle_field,
  left associativity,
  format "l .[ fld ]"
) : stdpp_scope.
Notation "v .[ fld ]" := (
  Val
    ( ValBlock Nongenerative (in_type "@atomic_loc" 0)
        ( @cons val v%V
            ( @cons val (ValInt (Z.of_nat fld))
                (@nil val)
            )
        )
    )
)(at level 2,
  fld custom mizzle_field,
  only printing,
  left associativity,
  format "v .[ fld ]"
) : expr_scope.
Notation "e .[ fld ]" := (
  Block
    ImmutableNongenerative
    (in_type "@atomic_loc" 0)
    ( @cons expr e%E
        ( @cons expr (Val (ValInt (Z.of_nat fld)))
            (@nil expr)
        )
    )
)(at level 2,
  fld custom mizzle_field,
  left associativity,
  format "e .[ fld ]"
) : expr_scope.
Notation "v .[ fld ]" := (
  ValBlock Nongenerative (in_type "@atomic_loc" 0)
    ( @cons val v%V
        ( @cons val (ValInt (Z.of_nat fld))
            (@nil val)
        )
    )
)(at level 2,
  fld custom mizzle_field,
  left associativity,
  format "v .[ fld ]"
) : val_scope.

Notation "'contents'" := (
  in_type "@ref" 0
)(in custom mizzle_field
).
Notation "'ref' e" := (
  Block Mutable (in_type "@ref" 0) (@cons expr e%E (@nil expr))
)(at level 10
) : expr_scope.
Notation "! e" := (
  GetField NotAtomic e%E (Val (ValInt (Z.of_nat (in_type "@ref" 0))))
)(at level 9,
  right associativity,
  format "! e"
) : expr_scope.
Notation "e1 <- e2" := (
  SetField NotAtomic e1%E (Val (ValInt (Z.of_nat (in_type "@ref" 0)))) e2%E
)(at level 80,
  format "'[hv' '[hv' '[' e1 ']'  '/  ' <-  ']' '/  ' '[' e2 ']' ']'"
) : expr_scope.

(* The atomic counterparts, for [Atomic.get] / [Atomic.set]: an OCaml
   ['a Atomic.t] is represented by the very same [@ref] block, so these differ
   from [!] and [<-] only in the atomicity flag. The flag is not operationally
   observable -- both take the same step -- but [logic/race.v] reads it, and
   marking these non-atomic would report a data race between two [Atomic.get]s. *)
Notation "!ᵃᵗ e" := (
  GetField Atomic e%E (Val (ValInt (Z.of_nat (in_type "@ref" 0))))
)(at level 9,
  right associativity,
  format "!ᵃᵗ e"
) : expr_scope.
Notation "e1 <-ᵃᵗ e2" := (
  SetField Atomic e1%E (Val (ValInt (Z.of_nat (in_type "@ref" 0)))) e2%E
)(at level 80,
  format "'[hv' '[hv' '[' e1 ']'  '/  ' <-ᵃᵗ  ']' '/  ' '[' e2 ']' ']'"
) : expr_scope.

Notation "'None'" := (
  in_type "option" 0
)(in custom mizzle_tag
).
Notation "'Some'" := (
  in_type "option" 1
)(in custom mizzle_tag
).

Notation "[ ]" := (
  Val (ValBlock Nongenerative (in_type "@list" 0) (@nil val))
)(format "[ ]"
) : expr_scope.
Notation "[ ]" := (
  ValBlock Nongenerative (in_type "@list" 0) (@nil val)
)(format "[ ]"
) : val_scope.
Notation "e1 :: e2" := (
  Block ImmutableNongenerative (in_type "@list" 1)
    ( @cons expr e1%E
        ( @cons expr e2%E
            (@nil expr)
        )
    )
)(at level 60,
  right associativity,
  format "e1  ::  e2"
) : expr_scope.
Notation "v1 :: v2" := (
  ValBlock Nongenerative (in_type "@list" 1)
    ( @cons val v1%V
        ( @cons val v2%V
            (@nil val)
        )
    )
)(at level 60,
  right associativity,
  format "v1  ::  v2"
) : val_scope.
