let main () =
  let len = 2000 in
  let a = Array.make len 0 in
  for i = 0 to len - 1 do
    a.(i) <- i
  done;
  Drb.parallel_for 1000 (fun i -> a.((2 * i) + 1) <- a.(i) + 1)
