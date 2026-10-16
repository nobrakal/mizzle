(* A simplified lock-free (Treiber) stack, exposed through a single [op]
   entry point dispatching [Push]/[Pop], for the linearizability framework.
   The sequential model is pure_logic/stack_model.v. *)

type 'a t = 'a list Atomic.t

type 'a req =
  | Push of 'a
  | Pop

let create () =
  Atomic.make []

let push t v =
  let before = Atomic.get t in
  let after = v :: before in
  let _ = Atomic.compare_and_set t before after in
  ()

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
