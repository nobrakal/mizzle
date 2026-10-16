(* The buggy concurrent stack of the paper's key-ideas section
   (fig-buggy-stack). A variant of Treiber's stack, exposed through a single
   [op] entry point dispatching [Push]/[Pop], for the linearizability
   framework. The sequential model is pure_logic/stack_model.v.

   The bug is in [push]: it snapshots the head into [xs] and builds [ys] from
   it, but its compare-and-set tests against a *fresh* read of [t] rather than
   the snapshot [xs]. So a concurrent push slipped in between is silently
   lost. *)

type 'a t = 'a list Atomic.t

type 'a req =
  | Push of 'a
  | Pop

let create () =
  Atomic.make []

let rec push t v =
  let xs = Atomic.get t in
  let ys = v :: xs in
  if not (Atomic.compare_and_set t (Atomic.get t) ys) then
    push t v

let rec pop t =
  match Atomic.get t with
  | [] ->
      None
  | hd :: tail as before ->
      if Atomic.compare_and_set t before tail then
        Some hd
      else
        pop t

let op t req =
  match req with
  | Push x ->
      push t x;
      None
  | Pop ->
      pop t

let client () =
  let t = create () in
  let f i = push t i; assert (pop t <> None) in
  ignore (Domain.spawn (fun () -> f 1));
  f 2
