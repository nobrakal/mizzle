(** Tactic overrides and ambient flags for Mizzle's language.

    A copy of Zoo's [zoo/tactics.v] and [zoo/options.v], restricted to what the
    language and the logic on top of it use. Some of these override an stdpp
    tactic of the same name with a different argument shape ([destruct_decide]
    takes the proposition here, not the [Decision] term), so — exactly as with
    Zoo's [options] — a require block that also pulls in stdpp modules must
    import this one *last*, or stdpp's versions end up on top. *)

From Stdlib.ssr Require Import
  ssreflect.
From Stdlib.Program Require Import
  Tactics.

From mizzle.lang Require Import
  prelude.

#[export] Set Default Proof Using "Type*".
#[export] Set Suggest Proof Using.

#[export] Set Bullet Behavior "Strict Subproofs".

#[export] Unset SsrOldRewriteGoalsOrder.

#[export] Set Printing Projections.

(** * Tactics

    [ssreflect] shadows [stdpp]'s [done], which is the stronger of the two and
    the one the proofs are written against. *)

Ltac done :=
  stdpp.tactics.done.

Tactic Notation "simplify" :=
  repeat (destruct_conjs; destruct_or?);
  simplify_eq/=.

Tactic Notation "invert" ident(H) "as" simple_intropattern(pat) :=
  inversion H as pat; clear H; simplify_eq/=.
Tactic Notation "invert" ident(H) :=
  invert H as [].

Tactic Notation "destruct_decide" constr(P) "as" simple_intropattern(pat1) "|" simple_intropattern(pat2) :=
  destruct (decide P) as [pat1 | pat2].
Tactic Notation "destruct_decide" constr(P) "as" simple_intropattern(pat) :=
  destruct_decide P as pat | pat.
Tactic Notation "destruct_decide" constr(P) :=
  let H := fresh "H" in
  destruct_decide P as H | H.
