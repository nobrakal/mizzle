type t =
  { mutable f1: int
  ; f2: int
  }

let test1 () =
  let t1 = { f1= 0; f2= 1 } in
  let _ = t1.f1 in
  t1.f1 <- 0

let test2 t =
  { t with f1= 0 }

let test3 () =
  { { f1= 0; f2= 0 } with f1= 0 }
