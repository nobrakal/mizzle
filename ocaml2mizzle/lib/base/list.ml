include Stdlib.List

let rec make n x =
  if n <= 0 then
    []
  else
    x :: make (n - 1) x

let[@tail_mod_cons] rec interleave x xs =
  match xs with
  | []
  | [_] ->
      xs
  | x0 :: xs ->
      x0 :: x :: interleave x xs
