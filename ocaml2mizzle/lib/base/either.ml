include Stdlib.Either

let get_left ~right = function
  | Left x ->
      x
  | Right _ ->
      right
let get_right ~left = function
  | Left _ ->
      left
  | Right x ->
      x

let get_left' right = function
  | Left x ->
      x
  | Right x ->
      right x
let get_right' left = function
  | Left x ->
      left x
  | Right x ->
      x
