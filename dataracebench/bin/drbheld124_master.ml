(* The master thread is the second, calling thread of [Drb.par]. [omp master]
   has no implicit barrier, so the other thread may read [init] while the
   master writes it. The uninitialised C [init] starts at [0]. *)

let main () =
  let init = ref 0 in
  Drb.par
    (fun () ->
      let _local = !init in
      ())
    (fun () ->
      init := 10;
      let _local = !init in
      ())
