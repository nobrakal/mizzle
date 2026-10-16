let main () =
  let len = 20000 in
  let a = Array.make len 0 in
  let b = Array.make len 0 in
  for i = 0 to len - 1 do
    a.(i) <- i;
    b.(i) <- i + 1
  done;
  Drb.parallel_for (len - 64) (fun i -> a.(i + 64) <- a.(i) + b.(i))
