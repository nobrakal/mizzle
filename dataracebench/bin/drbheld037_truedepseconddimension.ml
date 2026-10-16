let main () =
  let n = 1000 in
  let m = 1000 in
  let b = Array.make_matrix n m 0 in
  for i = 0 to n - 1 do
    Drb.parallel_for (m - 1) (fun k ->
        let j = k + 1 in
        b.(i).(j) <- b.(i).(j - 1))
  done
