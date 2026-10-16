type t =
  | Ident of string
  | Dot of t * string

let separator =
  "٠"

let rec of_list acc = function
  | [] ->
      acc
  | str :: strs ->
      of_list (Dot (acc, str)) strs
let of_list = function
  | [] ->
      invalid_arg __FUNCTION__
  | str :: strs ->
      of_list (Ident str) strs

let rec to_list acc = function
  | Ident str ->
      str :: acc
  | Dot (t, str) ->
      to_list (str :: acc) t
let to_list =
  to_list []

let to_string t =
  t
  |> to_list
  |> String.concat separator

let pp ppf t =
  t
  |> to_string
  |> Fmt.string ppf

module Builtin = struct
  let diverge =
    Ident "diverge"
  let assert_ =
    Ident "assert"
  let assume =
    Ident "assume"
end
