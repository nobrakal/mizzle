(* A simplified lock-free hash table (open chaining over a fixed set of
   atomic buckets), exposed through a single [op] entry point dispatching
   [Add]/[Remove]/[Mem], for the linearizability framework. ocaml2mizzle-input
   ([cases]) version: a restricted subset of OCaml with monomorphic
   [int] keys and values and an identity hash over two buckets. *)

type bucket = Nil | Cons of int * int * bucket

type t = bucket Atomic.t array

type req =
  | Add of int * int
  | Remove of int
  | Mem of int

let create () = Array.init 16 (fun _ -> Atomic.make Nil)

let bucket t key = Array.get t (key land 15)

let rec assoc_mem key b =
  match b with
  | Nil -> false
  | Cons (k, _, rest) -> k == key || assoc_mem key rest

let mem t key =
  let b = bucket t key in
  assoc_mem key (Atomic.get b)

let rec try_add t key value =
  let b = bucket t key in
  let old = Atomic.get b in
  if assoc_mem key old then false
  else if Atomic.compare_and_set b (Atomic.get b) (Cons (key, value, old)) then
    true
  else try_add t key value

let rec remove_list key b =
  match b with
  | Nil -> Nil
  | Cons (k, v, rest) ->
      if k == key then rest else Cons (k, v, remove_list key rest)

let rec try_remove t key =
  let b = bucket t key in
  let old = Atomic.get b in
  if not (assoc_mem key old) then false
  else if Atomic.compare_and_set b old (remove_list key old) then true
  else try_remove t key

let op t req =
  match req with
  | Add (k, v) -> try_add t k v
  | Remove k -> try_remove t k
  | Mem k -> mem t k
