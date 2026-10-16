(** Classes and arithmetic exports needed by Mizzle's language.

    Copied from Zoo's [zoo/common/typeclasses.v], [zoo/common/string.v],
    [zoo/common/binder.v] and [zoo/common/math.v], restricted to what the
    language and the logic on top of it use. Like Zoo's [common/], this file is
    re-exported by [syntax.v], so [≈], [≉] and [≟] are available to every
    client of the language. *)

From Stdlib Require Export
  ZifyNat.

From stdpp Require Export
  numbers
  strings
  binders.

From mizzle.lang Require Import
  prelude.
From mizzle.lang Require Import
  options.

(** * [Similar] and [Nonsimilar]

    Physical equality is not an equivalence, so it cannot be phrased with [=]
    or [≡]: [similar] is the "physically equal" relation and [nonsimilar] the
    "physically distinct" one, and neither is the negation of the other (both
    fail on values whose comparison is unspecified). *)

Class Similar X :=
  similar : X → X → Prop.
#[global] Arguments similar {_ _} !_ !_ / : simpl nomatch, assert.
Infix "≈" :=
  similar
( at level 70,
  no associativity
) : stdpp_scope.
Infix "≈@{ X }" := (
  @similar X _
)(at level 70,
  only parsing,
  no associativity
) : stdpp_scope.
Notation "(≈)" :=
  similar
( only parsing
) : stdpp_scope.
Notation "(≈@{ X } )" := (
  @similar X _
)( only parsing
) : stdpp_scope.
Notation "( x1 ≈.)" := (
  similar x1
)(only parsing
) : stdpp_scope.
Notation "(.≈ x2 )" := (
  λ x1, similar x1 x2
)(only parsing
) : stdpp_scope.

Class Nonsimilar X :=
  nonsimilar : X → X → Prop.
#[global] Arguments nonsimilar {_ _} !_ !_ / : simpl nomatch, assert.
Infix "≉" :=
  nonsimilar
( at level 70,
  no associativity
) : stdpp_scope.
Infix "≉@{ X }" := (
  @nonsimilar X _
)(at level 70,
  only parsing,
  no associativity
) : stdpp_scope.
Notation "(≉)" :=
  nonsimilar
( only parsing
) : stdpp_scope.
Notation "(≉@{ X } )" := (
  @nonsimilar X _
)( only parsing
) : stdpp_scope.
Notation "( x1 ≉.)" := (
  nonsimilar x1
)(only parsing
) : stdpp_scope.
Notation "(.≉ x2 )" := (
  λ x1, nonsimilar x1 x2
)(only parsing
) : stdpp_scope.

(** * [Beq]

    A boolean equality test tied to propositional equality, used by the
    capture-avoiding substitution of [syntax.v] and by pattern matching in
    [semantics.v]. *)

Class Beq {X} :=
  { beq : X → X → bool
  ; beq_spec x1 x2 :
      beq x1 x2 = true ↔
      x1 = x2
  }.
#[global] Arguments Beq : clear implicits.
#[global] Arguments beq {_ _} !_ !_ / : simpl nomatch, assert.

Infix "≟" :=
  beq
( at level 30,
  no associativity
) : stdpp_scope.
Infix "≟@{ X }" := (
  @beq X _
)(at level 30,
  only parsing,
  no associativity
) : stdpp_scope.
Notation "(≟)" :=
  beq
( only parsing
) : stdpp_scope.
Notation "(≟@{ X } )" := (
  @beq X _
)( only parsing
) : stdpp_scope.
Notation "( x1 ≟.)" := (
  beq x1
)(only parsing
) : stdpp_scope.
Notation "(.≟ x2 )" := (
  λ x1, beq x1 x2
)(only parsing
) : stdpp_scope.

#[global] Program Instance nat_beq : Beq nat :=
  {|beq := Nat.eqb
  |}.
Next Obligation.
  apply Nat.eqb_eq.
Qed.

#[global] Program Instance string_beq : Beq string :=
  {|beq := String.eqb
  |}.
Next Obligation.
  apply String.eqb_eq.
Qed.

#[global] Program Instance binder_beq : Beq binder :=
  {|beq bdr1 bdr2 :=
      match bdr1, bdr2 with
      | BAnon, BAnon =>
          true
      | BNamed str1, BNamed str2 =>
          str1 ≟ str2
      | _, _ =>
          false
      end
  |}.
Next Obligation.
  naive_solver.
Qed.
Next Obligation.
  naive_solver.
Qed.
Next Obligation.
  intros [] [] => //=.
  rewrite beq_spec. naive_solver.
Qed.

(** * Arithmetic

    [b2n_inj] is resolved by typeclass search behind [inj] when the
    physical-equality material compares the [Nat.b2n] encodings of two
    booleans. *)

#[global] Instance b2n_inj :
  Inj (=) (=) Nat.b2n.
Proof.
  intros [] []; done.
Qed.
