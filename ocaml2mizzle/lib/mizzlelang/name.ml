type t =
  string

let internal =
  Printf.sprintf "@%s"
let temporary =
  internal "tmp"

module Hashtbl =
  Hashtbl.Make(String)
module Hashset =
  Hashset.Make(String)
