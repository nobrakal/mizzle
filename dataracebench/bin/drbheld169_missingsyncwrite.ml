let main () =
  let n = 8 in
  let r1 = Array.make n 0 in
  let r = Array.make (n * n * n) 0 in
  for i = 0 to n - 1 do
    for j = 0 to n - 1 do
      for k = 0 to n - 1 do
        r.((((i * n) + j) * n) + k) <- i
      done
    done
  done;
  Drb.parallel_for (n - 2) (fun p ->
      let i = p + 1 in
      for j = 1 to n - 2 do
        for k = 0 to n - 1 do
          r1.(k) <-
            r.((((i * n) + (j - 1)) * n) + k)
            + r.((((i * n) + (j + 1)) * n) + k)
            + r.(((((i - 1) * n) + j) * n) + k)
            + r.(((((i + 1) * n) + j) * n) + k)
        done
      done)
