(** Structural equality, copied from Zoo's
    [zoo/program_logic/structural_equality.v] — the program text and the
    [AsValRecs'] instances and [expr_scope] notations that let the tactics and
    the generated code step through it, without that file's WP specs. See
    [stdlib/structeq.v] for the goal-mode spec. *)

From mizzle.lang Require Import
  instances.

#[local] Definition __mizzle_recs := (
  recs: "structeq" "v1" "v2" =>
    if: IsImmediate "v1" then
      if: IsImmediate "v2" then
        "v1" == "v2"
      else
        false
    else if: IsImmediate "v2" then
      false
    else (
      GetTag "v1" == GetTag "v2" and
      let: "sz" := GetSize "v1" in
      "sz" == GetSize "v2" and
      "structeq_aux" "v1" "v2" "sz"
    )
  and: "structeq_aux" "v1" "v2" "i" =>
    if: "i" == 0 then
      true
    else
      let: "i" := "i" - 1 in
      "structeq" (GetField NotAtomic "v1" "i") (GetField NotAtomic "v2" "i") and
      "structeq_aux" "v1" "v2" "i"
)%mizzle_recs.
Definition structeq :=
  ValRecs 0 __mizzle_recs.
#[local] Definition structeq_aux :=
  ValRecs 1 __mizzle_recs.
#[global] Instance :
  AsValRecs' structeq 0 __mizzle_recs [
    structeq ;
    structeq_aux
  ].
Proof.
  done.
Qed.
#[global] Instance :
  AsValRecs' structeq_aux 1 __mizzle_recs [
    structeq ;
    structeq_aux
  ].
Proof.
  done.
Qed.

Notation "e1 = e2" := (
  App (App (Val structeq) e1%E) e2%E
)(at level 70,
  no associativity
) : expr_scope.
Notation "e1 ≠ e2" := (
  Unop UnopNeg (App (App (Val structeq) e1%E) e2%E)
)(at level 70,
  no associativity
) : expr_scope.

#[global] Opaque structeq.
