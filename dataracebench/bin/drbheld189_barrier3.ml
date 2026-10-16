(* The two [omp barrier]s split the parallel region into three [Drb.par]
   phases; locks stay held across phases. The [printf]s reading [x] are
   dropped. *)

let barrier_start l0 l1 l2 tid =
  if tid = 0 then (
    Mutex.lock l0;
    Mutex.lock l2)
  else if tid = 1 then Mutex.lock l1

let barrier_stop l0 l1 l2 tid =
  if tid = 0 then (
    Mutex.unlock l0;
    Mutex.unlock l2)
  else if tid = 1 then Mutex.unlock l1

let barrier_wait l0 l1 tid =
  if tid = 0 then (
    Mutex.unlock l0;
    Mutex.lock l1;
    Mutex.lock l0;
    Mutex.unlock l1)
  else if tid = 1 then (
    Mutex.lock l0;
    Mutex.unlock l1;
    Mutex.unlock l0;
    Mutex.lock l1)

let main () =
  let n = 2 in
  let x = ref 1 in
  let l0 = Mutex.create () in
  let l1 = Mutex.create () in
  let l2 = Mutex.create () in
  Drb.par
    (fun () -> barrier_start l0 l1 l2 0)
    (fun () -> barrier_start l0 l1 l2 1);
  let body tid =
    for _i = 0 to n - 1 do
      barrier_wait l0 l1 tid;
      if tid = 0 then x := 0;
      barrier_wait l0 l1 tid;
      barrier_wait l0 l1 tid;
      if tid = 1 then x := 1;
      barrier_wait l0 l1 tid
    done
  in
  Drb.par (fun () -> body 0) (fun () -> body 1);
  Drb.par
    (fun () -> barrier_stop l0 l1 l2 0)
    (fun () -> barrier_stop l0 l1 l2 1)
