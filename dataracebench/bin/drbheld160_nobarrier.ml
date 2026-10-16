(* The number of teams and the [distribute] schedule are implementation
   defined: this port uses two one-thread teams and a static block
   distribution of the 16 iterations. In each [distribute] loop, the first
   team takes iterations [0..7] and the second [8..15]; the second loop runs
   downwards, so its iteration [k] is index [m - 1 - k]. With no barrier
   between the two loops, the teams form a [Drb.par], not two
   [Drb.parallel_for]s (whose implicit barriers would remove the race). *)

let main () =
  let n = 100 in
  let m = 16 in
  let a = 2 in
  let b = Array.make m 0 in
  let c = Array.make m 2 in
  let temp = Array.make m 0 in
  let team lo hi =
    for _j = 0 to n - 1 do
      for i = lo to hi do
        temp.(i) <- b.(i) + c.(i)
      done;
      for k = lo to hi do
        let i = m - 1 - k in
        b.(i) <- temp.(i) * a
      done
    done
  in
  Drb.par (fun () -> team 0 7) (fun () -> team 8 15)
