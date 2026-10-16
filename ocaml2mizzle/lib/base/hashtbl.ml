include Stdlib.Hashtbl

let create () =
  create 17

let is_empty t =
  length t = 0

let add_update t k init fn =
  match find_opt t k with
  | None ->
      add t k init ;
      init
  | Some v ->
      let v = fn v in
      replace t k v ;
      v

let map_list fn t =
  fold (fun k v acc -> fn k v :: acc) t []

let keys t =
  map_list (fun k _v -> k) t

include Hashtbl_intf

module Make
  (H : HashedType)
: S with type key = H.t
= struct
  include Make(H)

  let create () =
    create 17

  let is_empty t =
    length t = 0

  let add_update t k init fn =
    match find_opt t k with
    | None ->
        add t k init ;
        init
    | Some v ->
        let v = fn v in
        replace t k v ;
        v

  let map_list fn t =
    fold (fun k v acc -> fn k v :: acc) t []

  let keys t =
    map_list (fun k _v -> k) t
end
