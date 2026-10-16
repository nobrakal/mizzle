(* The named critical sections [critical(A)] and [critical(B)] are two
   distinct mutexes [a] and [b], so they do not exclude each other. The
   final [printf] reading [x] is dropped. *)

let main () =
  let x = ref 0 in
  let s = ref 0 in
  let a = Mutex.create () in
  let b = Mutex.create () in
  Drb.par
    (fun () ->
      x := 1;
      Mutex.lock a;
      s := 1;
      Mutex.unlock a)
    (fun () ->
      let fin = ref false in
      while not !fin do
        Mutex.lock b;
        if !s <> 0 then fin := true;
        Mutex.unlock b
      done;
      x := 2)
