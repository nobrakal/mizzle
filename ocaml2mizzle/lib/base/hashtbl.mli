include module type of struct
  include Stdlib.Hashtbl
end

val create :
  unit -> ('a, 'b) t

val is_empty :
  ('a, 'b) t -> bool

val add_update :
  ('a, 'b) t -> 'a -> 'b -> ('b -> 'b) -> 'b

val map_list :
  ('a -> 'b -> 'c) -> ('a, 'b) t -> 'c list

val keys :
  ('a, 'b) t -> 'a list

include module type of struct
  include Hashtbl_intf
end

module Make
  (H : HashedType)
: S with type key = H.t
