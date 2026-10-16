let main () =
  let len = 100 in
  let a = Array.make len 0 in
  let x = ref 10 in
  Drb.parallel_for len (fun i ->
      a.(i) <- !x;
      x := i)
