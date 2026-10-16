let main () =
  let c = 1 in
  let n = 20 in
  let nsteps = 100 in
  let b = Array.make (2 * n) 0 in
  let u = Array.make 2 0 in
  u.(1) <- n - 2;
  for i = 1 to n - 2 do
    b.(u.(1) + i) <- 1;
    b.(u.(0) + i) <- 1
  done;
  b.(u.(0)) <- 1;
  b.(u.(0) + n - 1) <- 1;
  b.(u.(1)) <- 1;
  b.(u.(1) + n - 1) <- 1;
  let p = ref 0 in
  for _t = 0 to nsteps - 1 do
    Drb.parallel_for (n - 2) (fun k ->
        let i = k + 1 in
        b.(u.(1 - !p) + i) <-
          b.(u.(!p) + i)
          + (c
             * (b.(u.(!p) + i - 1) + b.(u.(!p) + i + 1) - (2 * b.(u.(!p) + i)))));
    p := 1 - !p
  done
