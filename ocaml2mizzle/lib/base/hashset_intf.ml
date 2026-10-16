module type S = sig
  type elt

  type t

  val create :
    unit -> t

  val singleton :
    elt -> t

  val add :
    t -> elt -> unit

  val to_list :
    t -> elt list
end
