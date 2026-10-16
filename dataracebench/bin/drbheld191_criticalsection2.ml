(* The named critical sections [critical(A)] and [critical(B)] are two
   distinct mutexes [a] and [b], so they do not exclude each other. The
   [firstprivate] [r] becomes one local [ref] per section. Both sections
   loop forever. *)

let main () =
  let cap = 10 in
  let size = ref 0 in
  let a = Mutex.create () in
  let b = Mutex.create () in
  Drb.par
    (fun () ->
      let r = ref 0 in
      while true do
        Mutex.lock a;
        if !size < cap then size := !size + 1;
        Mutex.unlock a;
        for _i = 0 to 999 do
          r := (!r + 1) mod 10
        done
      done)
    (fun () ->
      let r = ref 0 in
      while true do
        Mutex.lock b;
        if !size > 0 then size := !size - 1;
        Mutex.unlock b;
        for _i = 0 to 999 do
          r := (!r + 1) mod 10
        done
      done)
