let main () =
  let in_len = 1000 in
  let out_len = ref 0 in
  let input = Array.make in_len 0 in
  let output = Array.make in_len 0 in
  for i = 0 to in_len - 1 do
    input.(i) <- i
  done;
  Drb.parallel_for in_len (fun i ->
      let idx = !out_len in
      out_len := idx + 1;
      output.(idx) <- input.(i))
