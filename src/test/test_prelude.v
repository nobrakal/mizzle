(** * Preamble for the [src/test] examples.

    Builds on [mizzle.logic.prelude] (iris proof mode + MizzleLang syntax + goal logic
    and [g_*] tactics) and adds the [stuck] reasoning mode every test uses.

    Case-specific extras stay in the individual files: [negation] for the
    negation examples, [mizzle.stdlib] [assert]/[trace]/[rand], and any
    iris libraries a particular example needs. *)

From mizzle.logic Require Export prelude.
From mizzle.logic Require Export stuck.
