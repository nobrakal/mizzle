let n = 180

let main () =
  let index_set = Array.make n 0 in
  for g = 0 to 29 do
    let start = 521 + (338 * (g / 6)) + (26 * (g mod 6)) in
    for k = 0 to 5 do
      index_set.((6 * g) + k) <- start + (2 * k)
    done
  done;
  index_set.(53) <- 923;
  let base = Array.make (2013 + 12 + 1) 0 in
  for i = 521 to 2025 do
    base.(i) <- i
  done;
  Drb.parallel_for_chunked 1 n (fun i ->
      let idx = index_set.(i) in
      base.(idx) <- base.(idx) + 1 + i;
      base.(idx + 12) <- base.(idx + 12) + 3 + i)
