module type S = sig
  include Stdlib.Hashtbl.S

  val create :
    unit -> 'a t

  val is_empty :
    'a t -> bool

  val add_update :
    'a t -> key -> 'a -> ('a -> 'a) -> 'a

  val map_list :
    (key -> 'a -> 'b) -> 'a t -> 'b list

  val keys :
    'a t -> key list
end
