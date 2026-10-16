(* A simplified lock-free (Michael-Scott) FIFO queue, exposed through a
   single [op] entry point dispatching [Enq]/[Deq], for the linearizability
   framework. ocaml2mizzle-input ([cases]) version: a restricted subset of OCaml. *)

type 'a node = Nil | Next of 'a * 'a node Atomic.t

type 'a t = {
  head : 'a node Atomic.t Atomic.t;
  tail : 'a node Atomic.t Atomic.t;
}

type 'a req =
  | Enq of 'a
  | Deq

let create () =
  let next = Atomic.make Nil in
  { head = Atomic.make next; tail = Atomic.make next }

let pop t =
  let old_head = Atomic.get t.head in
  match Atomic.get old_head with
  | Nil -> None
  | Next (value, next) ->
      if Atomic.compare_and_set t.head old_head next then
        Some value
      else
        None

let rec fix_tail tail new_tail =
  let old_tail = Atomic.get tail in
  match Atomic.get new_tail with
  | Nil ->
      if not (Atomic.compare_and_set tail old_tail new_tail) then
        fix_tail tail new_tail
  | Next _ -> ()

let rec find_tail_and_enq curr_end node =
  if not (Atomic.compare_and_set curr_end Nil node) then
    match Atomic.get curr_end with
    | Nil -> find_tail_and_enq curr_end node
    | Next (_, n) -> find_tail_and_enq n node

let push t value =
  let new_tail = Atomic.make Nil in
  let newnode = Next (value, new_tail) in
  let old_tail = Atomic.get t.tail in
  (if not (Atomic.compare_and_set old_tail Nil newnode) then
     match Atomic.get old_tail with
     | Nil -> find_tail_and_enq old_tail newnode
     | Next (_, n) -> find_tail_and_enq n newnode);
  if not (Atomic.compare_and_set t.tail old_tail new_tail) then
    fix_tail t.tail new_tail

let op t req =
  match req with
  | Enq x -> push t x; None
  | Deq -> pop t
