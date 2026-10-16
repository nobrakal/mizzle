let main () =
  let len = 10000 in
  let x = ref 0 in
  Drb.parallel_for len (fun i -> x := i)
