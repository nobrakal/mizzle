include module type of struct
  include Stdlib.Either
end

val get_left :
  right:'a -> ('a, 'b) t -> 'a
val get_right :
  left:'b -> ('a, 'b) t -> 'b

val get_left' :
  ('b -> 'a) -> ('a, 'b) t -> 'a
val get_right' :
  ('a -> 'b) -> ('a, 'b) t -> 'b
