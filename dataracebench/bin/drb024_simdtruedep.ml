let main () =
  let len = 100 in
  let a = Array.make len 0 in
  let b = Array.make len 0 in
  for i = 0 to len - 1 do
    a.(i) <- i;
    b.(i) <- i + 1
  done;
  Drb.parallel_for (len - 1) (fun i -> a.(i + 1) <- a.(i) + b.(i))
