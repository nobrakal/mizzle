type t =
  Parsetree.attribute

val mizzle :
  string
val has_mizzle :
  t list -> bool

val ignore :
  string
val has_ignore :
  t list -> bool

val force_record :
  string
val has_force_record :
  t list -> bool

val reveal :
  string
val has_reveal :
  t list -> bool

val opaque :
  string
val has_opaque :
  t list -> bool

type overwrite_kind =
  | Overwrite of Asttypes.rec_flag
  | Raw
val overwrite_kind_to_string :
  overwrite_kind -> string
val overwrite :
  string
val has_overwrite :
  t list -> (overwrite_kind * t) option
