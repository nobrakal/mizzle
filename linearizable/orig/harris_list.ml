(* A lock-free sorted linked-list set, after Harris ("A Pragmatic
   Implementation of Non-Blocking Linked-Lists", DISC 2001) with Michael's
   helping traversal ("High Performance Dynamic Lock-Free Hash Tables and
   List-Based Sets", SPAA 2002), exposed through a single [op] entry point
   dispatching [Add]/[Remove]/[Mem] like the hash-table cases.

   Each node is its [next] cell, a [link Atomic.t]. The cell's contents
   describe the successor: [Nil] at the end, [Cons (k, v, next)] for a node
   with key [k], value [v] and cell [next]. A node is logically deleted when
   its own cell holds [Marked succ], [succ] being the (frozen) unmarked
   contents it had. Harris's mark bit therefore lives in the same atomic word
   as the successor pointer, so a CAS that expects an unmarked successor fails
   once the node is marked. The list head [t] is a sentinel cell that is
   never marked. Keys are kept in increasing order.

   Written in the ocaml2mizzle-translatable subset of OCaml, like the [cases]
   variants derived from it ([linheld020]-[linheld023]). *)

type link = Nil | Cons of int * int * link Atomic.t | Marked of link

type t = link Atomic.t

type req =
  | Add of int * int
  | Remove of int
  | Mem of int

let create () = Atomic.make Nil

(* [find_from t prev key] walks from cell [prev] and returns [(prev, cur)]:
   [cur] is the unmarked contents read from [prev], either [Nil] or the
   first node with a key [>= key]. Marked nodes met on the way are unlinked;
   if [prev] itself turns out to be marked, the walk restarts from [t]. *)
let rec find_from t prev key =
  let cur = Atomic.get prev in
  match cur with
  | Marked _ -> find_from t t key
  | Nil -> (prev, cur)
  | Cons (k, _, next) ->
      (match Atomic.get next with
       | Marked succ ->
           if Atomic.compare_and_set prev cur succ then find_from t prev key
           else find_from t t key
       | _ -> if k < key then find_from t next key else (prev, cur))

let find t key = find_from t t key

let mem t key =
  let (_, cur) = find t key in
  match cur with
  | Cons (k, _, _) -> k == key
  | _ -> false

let rec try_add t key value =
  let (prev, cur) = find t key in
  let present =
    match cur with
    | Cons (k, _, _) -> k == key
    | _ -> false
  in
  if present then false
  else
    let node = Cons (key, value, Atomic.make cur) in
    if Atomic.compare_and_set prev cur node then true
    else try_add t key value

let rec try_remove t key =
  let (prev, cur) = find t key in
  match cur with
  | Cons (k, _, next) ->
      if k == key then
        (match Atomic.get next with
         | Marked _ -> try_remove t key
         | succ ->
             if Atomic.compare_and_set next succ (Marked succ) then begin
               (* Physical unlink, best effort: on failure a later [find]
                  unlinks the marked node. *)
               let _ = Atomic.compare_and_set prev cur succ in
               true
             end
             else try_remove t key)
      else false
  | _ -> false

let op t req =
  match req with
  | Add (k, v) -> try_add t k v
  | Remove k -> try_remove t k
  | Mem k -> mem t k
