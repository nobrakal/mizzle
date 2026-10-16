let main () =
  let len = 100 in
  let n = len in
  let m = len in
  let b = Array.make (n * m) 0 in
  Drb.parallel_for (n - 1) (fun k ->
      let i = k + 1 in
      for j = 0 to m - 1 do
        b.((i * m) + j) <- b.((i * m) + j - 1)
      done)
