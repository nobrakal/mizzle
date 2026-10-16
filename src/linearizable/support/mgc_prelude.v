(** * Preamble for most-general-client non-linearizability proofs.

    Builds on [mizzle.logic.prelude] (iris proof mode + MizzleLang syntax + goal logic
    and [g_*] tactics) and adds everything every [linNNN_mgc] solution shares:
    the MGC driver, the linearizability adequacy theorem, the pure
    linearizability checker, and the [rand]/[nondet_bool] generator support.

    A solution file then needs only its own two case-specific requires — the
    data-structure model (e.g. [stack_model] / [queue_opt_model]) and the case's
    [__code] / [__types] files. *)

From mizzle.logic Require Export prelude.
From mizzle.logic Require Export most_general_client adequacy_lin.
From mizzle.pure_logic Require Export linear linear_check.
From mizzle.stdlib Require Export rand.
(** For its [g_cas_succ] / [g_cas_fail] tactics, which step both the
    [atomic_loc٠cas] wrapper called by generated code and the primitive
    [CAS] (the primitive-only forms of [logic/goal_tactics] are
    [g_cas_prim_*]). *)
From mizzle.stdlib Require Export atomic_loc.

(** Helpers behind the [g_cas_*] wrapper tactics and the [goal_onecall_*]
    emits; not for hand application, so they do not show up in a [Search]
    for a CAS, an emit or the trace. *)
Add Search Blacklist "focused_atomic_loc_" "Trace_emit_" "goal_emit_".
