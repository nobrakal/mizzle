type 'a t =
  ('a, unit) Hashtbl.t

let create =
  Hashtbl.create

let add t elt =
  Hashtbl.replace t elt ()

let singleton elt =
  let t = create () in
  add t elt ;
  t

let to_list =
  Hashtbl.keys

let pp ?sep pp_elt =
  Fmt.hashtbl ?sep @@ fun ppf (elt, ()) ->
    pp_elt ppf elt

include Hashset_intf

module Make
  (H : Hashtbl.HashedType)
: S with type elt = H.t
= struct
  module Hashtbl =
    Hashtbl.Make(H)

  type elt =
    H.t

  type t =
    unit Hashtbl.t

  let create =
    Hashtbl.create

  let add t elt =
    Hashtbl.replace t elt ()

  let singleton elt =
    let t = create () in
    add t elt ;
    t

  let to_list =
    Hashtbl.keys
end
