let main () =
  let len = 1000 in
  let a = Array.make len 0 in
  a.(0) <- 2;
  Drb.parallel_for len (fun i -> a.(i) <- a.(i) + a.(0))
