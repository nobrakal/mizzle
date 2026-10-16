(* The [omp flush] is a no-op under sequential consistency and is dropped.
   The [reduction(+:sum)] becomes one private sum per thread, added up after
   the join. *)

let f1 lck q =
  Mutex.lock lck;
  q := 1;
  Mutex.unlock lck

let main () =
  let i = ref 0 in
  let lck = Mutex.create () in
  let sum1 = ref 0 in
  let sum2 = ref 0 in
  Drb.par
    (fun () ->
      f1 lck i;
      sum1 := !sum1 + !i)
    (fun () ->
      f1 lck i;
      sum2 := !sum2 + !i);
  let _sum = !sum1 + !sum2 in
  ()
