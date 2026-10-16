let main () =
  let len = 20000 in
  let a = Array.make len 0 in
  for i = 0 to len - 1 do
    a.(i) <- i
  done;
  Drb.parallel_for len (fun i -> a.(i) <- a.(i) + a.(64))
