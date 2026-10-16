type t =
  string

val internal :
  string -> t
val temporary :
  t

module Hashtbl :
  Hashtbl.S with type key = t
module Hashset :
  Hashset.S with type elt = t
