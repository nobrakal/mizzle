(** * Preamble for hash-table (array-backed) non-linearizability proofs.

    Extends [mgc_prelude] with everything the [linNNN] hash-table cases share:
    the [htbl_model], the [assume]/[array] stdlib support (program text and
    goal-mode specs, both in [mizzle.stdlib.array]), and the shared
    [htbl_array] helpers.

    A hash-table solution file then needs only its case's [__code] / [__types]
    requires. *)

(* [array] is exported *before* [mgc_prelude]/[htbl_array] so the mizzle
   logic notations (loaded last) win over its [↦]. *)
From mizzle.stdlib Require Export array.
From mizzle.pure_logic Require Export htbl_model.
From mizzle.stdlib Require Export assume array.
From mizzle.linearizable.support Require Export mgc_prelude htbl_array.
