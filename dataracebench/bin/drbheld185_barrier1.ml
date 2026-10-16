(* The unnamed [omp critical] is a single mutex [c]. The leading
   [omp barrier] only follows the thread-local [omp_get_thread_num] and is
   dropped, as are the [printf]s reading [x]. Each thread raises and lowers
   its own flag, so [mybarrier] never synchronises the two threads. *)

let raise c f =
  Mutex.lock c;
  assert (not !f);
  f := true;
  Mutex.unlock c

let lower c f =
  let fin = ref false in
  while not !fin do
    Mutex.lock c;
    if !f then (
      f := false;
      fin := true);
    Mutex.unlock c
  done

let mybarrier c f0 f1 tid =
  if tid = 0 then (
    raise c f0;
    lower c f0)
  else if tid = 1 then (
    raise c f1;
    lower c f1)

let main () =
  let n = 2 in
  let x = ref 1 in
  let f0 = ref false in
  let f1 = ref false in
  let c = Mutex.create () in
  let body tid =
    for _i = 0 to n - 1 do
      mybarrier c f0 f1 tid;
      if tid = 0 then x := 0;
      mybarrier c f0 f1 tid;
      mybarrier c f0 f1 tid;
      if tid = 1 then x := 1;
      mybarrier c f0 f1 tid
    done
  in
  Drb.par (fun () -> body 0) (fun () -> body 1)
