let main () =
  let n = 100 in
  let a = Array.make n 0 in
  Drb.parallel_for n (fun i ->
      a.(i) <- i;
      if i = 1 then a.(0) <- 1)
