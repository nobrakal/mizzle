include module type of struct
  include Stdlib.List
end

val make :
  int -> 'a -> 'a list

val interleave :
  'a -> 'a list -> 'a list
