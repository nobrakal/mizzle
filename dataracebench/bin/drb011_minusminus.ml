let main () =
  let len = 100 in
  let num_nodes = len in
  let num_nodes2 = ref 0 in
  let x = Array.make len 0 in
  for i = 0 to len - 1 do
    if i mod 2 = 0 then x.(i) <- 5 else x.(i) <- -5
  done;
  Drb.parallel_for num_nodes (fun i ->
      if x.(i) <= 0 then num_nodes2 := !num_nodes2 - 1)
