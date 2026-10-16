let main () =
  let tmp = ref 0 in
  let len = 100 in
  let a = Array.make len 0 in
  for i = 0 to len - 1 do
    a.(i) <- i
  done;
  Drb.parallel_for len (fun i ->
      tmp := a.(i) + i;
      a.(i) <- !tmp)
