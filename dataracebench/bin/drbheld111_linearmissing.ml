let main () =
  let len = 100 in
  let a = Array.make len 0 in
  let b = Array.make len 0 in
  let c = Array.make len 0 in
  let j = ref 0 in
  for i = 0 to len - 1 do
    a.(i) <- i;
    b.(i) <- i;
    c.(i) <- i
  done;
  Drb.parallel_for len (fun i ->
      c.(!j) <- c.(!j) + (a.(i) * b.(i));
      j := !j + 1)
