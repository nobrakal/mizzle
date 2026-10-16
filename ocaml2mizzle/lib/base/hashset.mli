type 'a t

val create :
  unit -> 'a t

val singleton :
  'a -> 'a t

val add :
  'a t -> 'a -> unit

val to_list :
  'a t -> 'a list

val pp :
  ?sep:unit Fmt.t -> 'a Fmt.t -> 'a t Fmt.t

include module type of struct
  include Hashset_intf
end

module Make
  (H : Hashtbl.HashedType)
: S with type elt = H.t
