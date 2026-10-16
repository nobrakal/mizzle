(** * Common preamble for dataracebench (race) proofs.

    Builds on [mizzle.logic.prelude] (iris proof mode + language syntax + goal
    logic and [g_*] tactics) and adds everything every [drbNNN__proof] shares:
    the race program logic and its adequacy theorem, [structeq], the DRB
    axioms, the [atomic_loc] CAS tactics, and [mizzle.lang.options].

    A proof file then needs only [mizzle.stdlib array] and its case's
    [__code] require — plus [mizzle.stdlib mutex] (and [mizzle.stdlib
    assert]) when the case's code uses locks (resp. [assert]). These stay in
    the individual files, before the [__code] require. *)

From mizzle.logic Require Export prelude.
From mizzle.logic Require Export race adequacy.
From mizzle.stdlib Require Export structeq.
From mizzle Require Export drb_axiom.
(** For its [g_cas_*] tactics, which step both the [atomic_loc٠cas] wrapper
    and the primitive [CAS], as in the linearizability proofs. *)
From mizzle.stdlib Require Export atomic_loc.
From mizzle.lang Require Export options.

(** Helpers behind the array and CAS tactics; not for hand application, so
    they do not show up in a [Search] for a loop, array or CAS redex. *)
Add Search Blacklist "focused_set_loop" "focused_fill_loop" "focused_fill_slice_loop"
  "focused_atomic_loc_".
