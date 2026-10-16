(** Smoke test for the lock-free hash table, run against the [orig] library
    ([orig/htbl.ml]) rather than any translatable [cases] version.

    Both this test and the [orig] library are separate from [cases], so
    [ocaml2mizzle --only=cases] does NOT translate either of them to Rocq. Run
    with [dune test] (or [dune exec test/test_htbl.exe]) from the
    [linearizable] project root. *)

module H = Orig.Htbl

let checks = ref 0

let check name cond =
  incr checks;
  if not cond then begin
    Printf.eprintf "FAIL: %s\n%!" name;
    exit 1
  end

(* Identity hash over a power-of-two bucket count, so keys equal mod [n]
   collide and exercise the [Cons] chaining / per-bucket CAS path. *)
let mk () : (int, int) H.t = H.create (fun k -> k) ( = ) 16

let sorted_keys t = List.sort compare (List.map fst (H.to_list t))

let () =
  let t = mk () in

  (* empty table *)
  check "fresh find_opt = None" (H.find_opt t 1 = None);
  check "fresh mem = false" (not (H.mem t 1));
  check "fresh to_list = []" (H.to_list t = []);

  (* try_add: first insert succeeds, duplicate key fails *)
  check "add 1 ok" (H.try_add t 1 100);
  check "add 2 ok" (H.try_add t 2 200);
  check "add dup 1 fails" (not (H.try_add t 1 999));
  check "find 1 = 100" (H.find_opt t 1 = Some 100);
  check "find 2 = 200" (H.find_opt t 2 = Some 200);
  check "mem 1" (H.mem t 1);
  check "mem missing" (not (H.mem t 3));

  (* collisions: 1 and 17 land in the same bucket (17 = 1 mod 16) *)
  check "add 17 ok (collides with 1)" (H.try_add t 17 1700);
  check "find 1 after collision" (H.find_opt t 1 = Some 100);
  check "find 17 after collision" (H.find_opt t 17 = Some 1700);
  check "keys so far" (sorted_keys t = [ 1; 2; 17 ]);

  (* try_set: replaces an existing value, fails on an absent key *)
  check "set 1 ok" (H.try_set t 1 101);
  check "find 1 = 101 after set" (H.find_opt t 1 = Some 101);
  check "set missing fails" (not (H.try_set t 99 0));
  check "set does not insert" (H.find_opt t 99 = None);

  (* try_remove: removes present key (incl. mid-chain), fails on absent *)
  check "remove 1 ok" (H.try_remove t 1);
  check "find 1 = None after remove" (H.find_opt t 1 = None);
  check "remove 1 again fails" (not (H.try_remove t 1));
  check "17 survives removal of colliding 1" (H.find_opt t 17 = Some 1700);
  check "keys after remove" (sorted_keys t = [ 2; 17 ]);

  (* multi-domain stress 1: 4 domains insert disjoint key ranges. *)
  let t2 = mk () in
  let n = 1000 in
  let domains =
    List.init 4 (fun d ->
        Domain.spawn (fun () ->
            for i = 0 to n - 1 do
              ignore (H.try_add t2 ((d * n) + i) (i + 1))
            done))
  in
  List.iter Domain.join domains;
  let all = H.to_list t2 in
  check "stress1 count" (List.length all = 4 * n);
  check "stress1 no loss / no dup"
    (List.sort compare (List.map fst all) = List.init (4 * n) (fun i -> i));
  check "stress1 all findable" (List.for_all (fun k -> H.mem t2 k) (List.map fst all));

  (* multi-domain stress 2: 4 domains race to add the SAME keys; each key
     must be added exactly once (try_add returns true for one winner). *)
  let t3 = mk () in
  let keys = 2000 in
  let wins =
    List.init 4 (fun _ ->
        Domain.spawn (fun () ->
            let w = ref 0 in
            for k = 0 to keys - 1 do
              if H.try_add t3 k k then incr w
            done;
            !w))
  in
  let total_wins = List.fold_left (fun a d -> a + Domain.join d) 0 wins in
  check "stress2 each key added exactly once" (total_wins = keys);
  check "stress2 final key set complete"
    (sorted_keys t3 = List.init keys (fun i -> i));
  check "stress2 values correct"
    (List.for_all (fun k -> H.find_opt t3 k = Some k) (List.init keys (fun i -> i)));

  Printf.printf "All %d checks passed.\n%!" !checks
