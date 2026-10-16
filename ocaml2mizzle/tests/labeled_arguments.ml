let test1 x1 ~x2 x3 ~x4 =
  let _ = x1 in
  let _ = x2 in
  let _ = x3 in
  let _ = x4 in
  ()

let test2 x1 ~x2:_ x3 ~x4 =
  let _ = x1 in
  let _ = x3 in
  let _ = x4 in
  ()

let test3 () =
  test1 1 ~x2:2 3 ~x4:4
