let incr_a a = a := !a + 1

let incr_b b = b := !b + 1

let main () =
  let a = ref 0 in
  let b = ref 0 in
  let lck = Mutex.create () in
  Drb.par
    (fun () ->
      Mutex.lock lck;
      incr_b b;
      incr_a a;
      Mutex.unlock lck)
    (fun () -> incr_b b)
