include Stdlib.Int

let rec to_decimal t acc =
  let div = div t 10 in
  let rem = rem t 10 in
  let acc = rem :: acc in
  if div == 0 then
    acc
  else
    to_decimal div acc
let to_decimal t =
  to_decimal t []

let to_string_subscript = function
  | 0 -> "₀"
  | 1 -> "₁"
  | 2 -> "₂"
  | 3 -> "₃"
  | 4 -> "₄"
  | 5 -> "₅"
  | 6 -> "₆"
  | 7 -> "₇"
  | 8 -> "₈"
  | _ -> "₉"
let to_string_subscript t =
  t
  |> to_decimal
  |> List.map to_string_subscript
  |> List.fold_left (^) ""
