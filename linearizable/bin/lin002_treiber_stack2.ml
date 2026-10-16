(* A simplified lock-free (Treiber) stack, exposed through a single [op]
   entry point dispatching [Push]/[Pop], for the linearizability framework.
   The sequential model is pure_logic/stack_model.v. *)

type 'a t = 'a list Atomic.t

type 'a req =
  | Push of 'a
  | Pop

let create () =
  Atomic.make []

let rec push t v =
  let before = Atomic.get t in
  let after = v :: before in
  if not (Atomic.compare_and_set t before after) then
    push t v

let pop t =
  match Atomic.get t with
  | [] ->
      None
  | hd :: tail ->
      Atomic.set t tail;
      Some hd

let op t req =
  match req with
  | Push x ->
      push t x;
      None
  | Pop ->
      pop t
