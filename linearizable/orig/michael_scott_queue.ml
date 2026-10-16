(* A self-contained Michael-Scott lock-free FIFO queue, ported from Saturn's
   [src/michael_scott_queue/michael_scott_queue.ml].

   Relative to the original, this is restricted to an ocaml2mizzle-translatable subset
   of OCaml: the [Backoff] dependency is dropped (a failed CAS just retries),
   the [Empty] exception and the [poly]/GADT machinery are replaced by the
   option-returning [pop_opt]/[peek_opt], [Atomic.make_contended] becomes
   [Atomic.make], and the nested [let rec] helpers are lifted to top level. *)

type 'a node = Nil | Next of 'a * 'a node Atomic.t

type 'a t = {
  head : 'a node Atomic.t Atomic.t;
  tail : 'a node Atomic.t Atomic.t;
}

let create () =
  let next = Atomic.make Nil in
  let head = Atomic.make next in
  let tail = Atomic.make next in
  { head; tail }

let is_empty t =
  match Atomic.get (Atomic.get t.head) with
  | Nil -> true
  | Next _ -> false

let rec pop_opt t =
  let old_head = Atomic.get t.head in
  match Atomic.get old_head with
  | Nil -> None
  | Next (value, next) ->
      if Atomic.compare_and_set t.head old_head next then
        Some value
      else
        pop_opt t

let peek_opt t =
  match Atomic.get (Atomic.get t.head) with
  | Nil -> None
  | Next (value, _) -> Some value

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
