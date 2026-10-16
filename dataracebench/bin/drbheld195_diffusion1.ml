let main () =
  let c = 1 in
  let n = 10 in
  let nsteps = 10 in
  let u1 = ref (Array.make n 0) in
  let u2 = ref (Array.make n 0) in
  for i = 1 to n - 2 do
    (!u1).(i) <- 1;
    (!u2).(i) <- (!u1).(i)
  done;
  (!u1).(0) <- 1;
  (!u1).(n - 1) <- 1;
  (!u2).(0) <- 1;
  (!u2).(n - 1) <- 1;
  for _t = 0 to nsteps - 1 do
    Drb.parallel_for (n - 2) (fun k ->
        let i = k + 1 in
        (!u2).(i) <-
          (!u1).(i)
          + (c * ((!u1).(i - 1) + (!u1).(i + 1) - (2 * (!u1).(i)))));
    let _tmp = !u1 in
    u1 := !u2
  done
