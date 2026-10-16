(* Shared helper *)

open Domainslib.Task

let run_with_pool (f:pool -> unit) : unit =
  let p = setup_pool ~num_domains:4 () in
  run p (fun () -> f p);
  teardown_pool p

(* OpenMP-style parallel loop: iterates i over [start, finish), i.e. the
   upper bound is EXCLUSIVE (like `for (i = start; i < finish; i++)`),
   unlike Domainslib's [parallel_for] whose ~finish is inclusive. *)
let parallel_for_excl ?chunk_size ~start ~finish ~body pool =
  if finish > start then
    parallel_for ?chunk_size ~start ~finish:(finish - 1) ~body pool

(* Convenience wrapper: set up a pool and iterate i over [0, n). *)
let parallel_for n body =
  run_with_pool (fun pool ->
    parallel_for_excl ~start:0 ~finish:n ~body pool)

(* Like [parallel_for], but with an explicit chunk size — the OCaml analogue
   of OpenMP's `schedule(static,c)` (e.g. `schedule(static,1)` in DRB005,
   used there to maximize the chance that dependent iterations land on
   different threads). *)
let parallel_for_chunked chunk n body =
  run_with_pool (fun pool ->
    parallel_for_excl ~chunk_size:chunk ~start:0 ~finish:n ~body pool)

(* OpenMP `parallel sections` with two sections: run [f] in a fresh domain
   and [g] in the current one, then join, with a barrier at the end. *)
let par f g =
  let t = Domain.spawn f in
  g ();
  Domain.join t
