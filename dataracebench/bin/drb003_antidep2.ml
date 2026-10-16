let main () =
  let len = 20 in
  let a = Array.make_matrix len len 1 in
  Drb.parallel_for (len - 1) (fun i ->
      for j = 0 to len - 1 do
        a.(i).(j) <- a.(i).(j) + a.(i + 1).(j)
      done)
