(* A lock-free sorted linked-list set (Harris, DISC 2001; Michael, SPAA
   2002), exposed through a single [op] entry point dispatching
   [Add]/[Remove]/[Mem], for the linearizability framework. A node's cell
   holds its successor, or [Marked succ] once the node is deleted. The
   sequential model is pure_logic/htbl_model.v. *)

type link = Nil | Cons of int * int * link Atomic.t | Marked of link

type t = link Atomic.t

type req =
  | Add of int * int
  | Remove of int
  | Mem of int

let create () = Atomic.make Nil

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


let rec link prev cell node =
  let cur = Atomic.get prev in
  Atomic.set cell cur;
  if Atomic.compare_and_set prev cur node then true
  else link prev cell node

let try_add t key value =
  let (prev, cur) = find t key in
  let present =
    match cur with
    | Cons (k, _, _) -> k == key
    | _ -> false
  in
  if present then false
  else
    let cell = Atomic.make cur in
    let node = Cons (key, value, cell) in
    if Atomic.compare_and_set prev cur node then true
    else link prev cell node

let rec try_remove t key =
  let (prev, cur) = find t key in
  match cur with
  | Cons (k, _, next) ->
      if k == key then
        (match Atomic.get next with
         | Marked _ -> try_remove t key
         | succ ->
             if Atomic.compare_and_set next succ (Marked succ) then begin
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
