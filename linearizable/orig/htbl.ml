(* A self-contained lock-free hash table, ported from Saturn's
   [src/htbl/htbl.body.ml].

   Relative to the original, this is restricted to an ocaml2mizzle-translatable subset
   of OCaml and keeps only the lock-free open-chaining core:

     - buckets are a fixed array of [Atomic.t] cells, each holding an
       immutable association list ([Nil] / [Cons]); writers replace a whole
       bucket spine with a single [compare_and_set];
     - the GADT [tdt] spine (with its [`Nil_with_size]/[`Resize] type
       witnesses) collapses to a plain [bucket] variant, with [Cons] carrying
       a tuple instead of an inline record;
     - the [Backoff] dependency is dropped (a failed CAS just retries);
     - the [raise_notrace Not_found] / [poly] GADT machinery is replaced by
       option-returning [find_opt] and boolean [try_*] operations;
     - [Atomic.make_contended] becomes [Atomic.make], and the nested
       [let rec]/[@tail_mod_cons] helpers are lifted to top level.

   Dropped entirely (these have no lock-free analogue in the subset and are
   orthogonal to the bucket-level linearization points): incremental resizing
   ([finish]/[try_resize]/[split_all]/[merge_all]/[copy_all]), the [Size]
   counter, randomized resize triggers, snapshots ([to_seq]/[remove_all]),
   and [find_random]. The table therefore has a fixed number of buckets,
   which must be a power of two so that [hash key land (n-1)] indexes it. *)

type ('k, 'v) bucket =
  | Nil
  | Cons of 'k * 'v * ('k, 'v) bucket

type ('k, 'v) t = {
  buckets : ('k, 'v) bucket Atomic.t array;
  hash : 'k -> int;
  equal : 'k -> 'k -> bool;
}

(* [n] must be a power of two. *)
let create hash equal n =
  { buckets = Array.init n (fun _ -> Atomic.make Nil); hash; equal }

let bucket t key =
  Array.get t.buckets (t.hash key land (Array.length t.buckets - 1))

(* *)

let rec assoc_opt equal key b =
  match b with
  | Nil -> None
  | Cons (k, v, rest) -> if equal k key then Some v else assoc_opt equal key rest

let find_opt t key = assoc_opt t.equal key (Atomic.get (bucket t key))

let rec mem_list equal key b =
  match b with
  | Nil -> false
  | Cons (k, _, rest) -> equal k key || mem_list equal key rest

let mem t key = mem_list t.equal key (Atomic.get (bucket t key))

(* *)

(* Insert [key]/[value] if [key] is absent; returns whether it was added. *)
let rec try_add t key value =
  let b = bucket t key in
  let old = Atomic.get b in
  if mem_list t.equal key old then false
  else if Atomic.compare_and_set b old (Cons (key, value, old)) then true
  else try_add t key value

(* [remove_list eq k b] is [Some b'] where [b'] is [b] without the first
   binding of [k], or [None] if [k] is absent. *)
let rec remove_list equal key b =
  match b with
  | Nil -> None
  | Cons (k, v, rest) ->
      if equal k key then Some rest
      else (
        match remove_list equal key rest with
        | None -> None
        | Some rest' -> Some (Cons (k, v, rest')))

(* Remove [key] if present; returns whether it was removed. *)
let rec try_remove t key =
  let b = bucket t key in
  let old = Atomic.get b in
  match remove_list t.equal key old with
  | None -> false
  | Some next ->
      if Atomic.compare_and_set b old next then true else try_remove t key

(* [replace_list eq k v b] is [Some b'] where [b'] is [b] with the first
   binding of [k] re-pointed to [v], or [None] if [k] is absent. *)
let rec replace_list equal key value b =
  match b with
  | Nil -> None
  | Cons (k, v, rest) ->
      if equal k key then Some (Cons (k, value, rest))
      else (
        match replace_list equal key value rest with
        | None -> None
        | Some rest' -> Some (Cons (k, v, rest')))

(* Replace the value bound to an existing [key]; returns whether it existed. *)
let rec try_set t key value =
  let b = bucket t key in
  let old = Atomic.get b in
  match replace_list t.equal key value old with
  | None -> false
  | Some next ->
      if Atomic.compare_and_set b old next then true else try_set t key value

(* *)

(* Convenience snapshot for single-threaded inspection/tests (not part of the
   lock-free contract): the bindings reachable from each bucket, in no
   particular order. *)
let rec bucket_to_list b acc =
  match b with
  | Nil -> acc
  | Cons (k, v, rest) -> bucket_to_list rest ((k, v) :: acc)

let to_list t =
  let n = Array.length t.buckets in
  let rec loop i acc =
    if i >= n then acc
    else loop (i + 1) (bucket_to_list (Atomic.get (Array.get t.buckets i)) acc)
  in
  loop 0 []
