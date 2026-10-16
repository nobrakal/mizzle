(* The two [omp barrier]s split the parallel region into three [Drb.par]
   phases; locks stay held across phases. *)

let main () =
  let x = ref 1 in
  let l0 = Mutex.create () in
  let l1 = Mutex.create () in
  Drb.par (fun () -> Mutex.lock l0) (fun () -> Mutex.lock l1);
  Drb.par
    (fun () ->
      x := 0;
      Mutex.unlock l0;
      Mutex.lock l0)
    (fun () ->
      Mutex.unlock l1;
      Mutex.lock l1;
      x := 1);
  Drb.par (fun () -> Mutex.unlock l1) (fun () -> Mutex.unlock l0)
