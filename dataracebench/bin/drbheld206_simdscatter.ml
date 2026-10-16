let main () =
  let len = 20000 in
  let a = Array.make (2 * len) 0 in
  let b = Array.make len 0 in
  for i = 0 to (2 * len) - 1 do
    a.(i) <- i
  done;
  for i = 0 to len - 1 do
    b.(i) <- i + 1
  done;
  Drb.parallel_for len (fun i -> a.(i * 2) <- a.(i + 64) + b.(i))
