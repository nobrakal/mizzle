(* The leading [omp barrier] has nothing before it in the parallel region
   and is dropped. *)

let main () =
  let x = ref 1 in
  let l = Mutex.create () in
  Drb.par
    (fun () ->
      Mutex.lock l;
      x := 0;
      Mutex.unlock l)
    (fun () ->
      Mutex.lock l;
      Mutex.unlock l;
      x := 1)
