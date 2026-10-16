(** Mizzle-specific mapping of library names onto Rocq logical paths.

    Upstream [ocaml2zoo] emits requires against the [zoo] theory. Mizzle
    vendors the language instead, so the generated files must require
    [mizzle.lang] / [mizzle.stdlib]. This module holds that mapping, which
    [gen_mizzle.sh] used to apply as a post-processing pass over the generated
    [.v] files. *)

(** The logical path of Mizzle's vendored language. *)
val lang : string

(** The logical path of Mizzle's vendored program text. *)
val stdlib : string

(** What a library name is rewritten to. *)
type target =
  | Rename of string
      (** Rewrite the library, keep module names. *)
  | Rename_module of string * string
      (** Rewrite the library and collapse all its modules to one. *)
  | Drop
      (** Drop the require entirely. *)

(** Whether to emit (and require) the [__types] files. *)
val types : bool ref

(** [set_prefix path] prefixes the project's own libraries with [path], so that
    a dune library [cases] is required as [path.cases]. *)
val set_prefix : string -> unit

(** [add_override lib target] registers a per-project rewrite for [lib]. *)
val add_override : string -> target -> unit

(** [parse_override s] reads a command-line [lib=spec] pair, where [spec] is
    empty to drop, [path] to rename, or [path:module] to also collapse
    modules. *)
val parse_override : string -> (string * target, string) Either.t

(** [require lib mod_] is the Rocq [(path, module)] pair that [lib]'s module
    [mod_] must be required as, or [None] if the require is dropped. *)
val require : string -> string -> (string * string) option
