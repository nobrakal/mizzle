(** Notations and ambient scopes for Mizzle's language.

    A copy of Zoo's [zoo/prelude.v], restricted to what the language and the
    logic on top of it use. Zoo's split between [prelude.v] and [options.v] is
    kept as it is: [prelude] re-exports [ssreflect] and is what a file imports
    to write in that dialect, while [options] carries only the tactic
    overrides and the flags. Merging the two would hand [ssreflect]'s
    [rewrite] to every client of [options], which is not what Zoo does. *)

From Stdlib.ssr Require Export
  ssreflect.

From stdpp Require Export
  prelude.

(** [ssreflect] takes over [if]; [general_if_scope] restores the [Stdlib]
    reading. *)

Open Scope general_if_scope.

(** * Notations *)

Notation "￢ b" := (
  negb b
)(at level 30,
  right associativity,
  format "￢  b"
).

Coercion Z.of_nat : nat >-> Z.

Notation "₊ n" := (
  Z.to_nat n
)(at level 3,
  right associativity,
  format "₊ n"
) : stdpp_scope.
