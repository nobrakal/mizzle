(** * Common preamble for mizzle goal-based proofs.

    Re-exports the iris proof mode, the language *syntax*, and the goal-based
    program logic together with its [g_*] tactics, so a downstream file
    replaces the usual 4-line incantation with a single [Require Import].

    On the language: only [mizzle.lang.syntax] is needed here — it carries the
    AST ([val]/[location]/…) and all the notations. [mizzle.lang.instances] is
    *not* re-exported: its global instances are registered transitively (via
    [goal_tactics] and the logic modules that [Require] it), so instance
    resolution and the [g_*] tactics work without importing it by name. *)

From iris.proofmode Require Export base proofmode.
From mizzle.lang Require Export syntax.
From mizzle.logic Require Export interp goal goal_proof goal_tactics.
