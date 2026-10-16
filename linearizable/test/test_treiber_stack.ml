(** Smoke test for the Treiber stack, run against the [orig] library
    ([orig/treiber_stack.ml]) rather than the translatable [cases] version.

    Both this test and the [orig] library are separate from [cases], so
    [ocaml2mizzle --only=cases] does NOT translate either of them to Rocq. Run
    with [dune test] (or [dune exec test/test_treiber_stack.exe]) from the
    [linearizable] project root. *)

module S = Orig.Treiber_stack

let checks = ref 0

let check name cond =
  incr checks;
  if not cond then begin
    Printf.eprintf "FAIL: %s\n%!" name;
    exit 1
  end

let () =
  (* empty stack *)
  let t : int S.t = S.create () in
  check "fresh is_empty" (S.is_empty t);
  check "fresh peek_opt = None" (S.peek_opt t = None);
  check "fresh pop_opt = None" (S.pop_opt t = None);
  check "fresh pop_all = []" (S.pop_all t = []);

  (* push / peek / pop, LIFO order *)
  S.push t 1;
  S.push t 2;
  S.push t 3;
  check "not empty after push" (not (S.is_empty t));
  check "peek_opt top = 3" (S.peek_opt t = Some 3);
  check "peek does not pop" (S.peek_opt t = Some 3);
  check "pop_opt LIFO 3" (S.pop_opt t = Some 3);
  check "pop_opt LIFO 2" (S.pop_opt t = Some 2);
  check "pop_opt LIFO 1" (S.pop_opt t = Some 1);
  check "empty after draining" (S.is_empty t);
  check "pop_opt past end = None" (S.pop_opt t = None);

  (* pop_all returns a LIFO snapshot and empties the stack *)
  S.push t 10;
  S.push t 20;
  S.push t 30;
  check "pop_all LIFO" (S.pop_all t = [ 30; 20; 10 ]);
  check "empty after pop_all" (S.is_empty t);

  (* small multi-domain stress: 4 pushers, then drain on the main domain *)
  let t2 : int S.t = S.create () in
  let n = 1000 in
  let domains =
    List.init 4 (fun d ->
        Domain.spawn (fun () ->
            for i = 0 to n - 1 do
              S.push t2 ((d * n) + i)
            done))
  in
  List.iter Domain.join domains;
  let all = S.pop_all t2 in
  check "stress count" (List.length all = 4 * n);
  check "stress no loss / no dup"
    (List.sort compare all = List.init (4 * n) (fun i -> i));
  check "stress empty after drain" (S.is_empty t2);

  Printf.printf "All %d checks passed.\n%!" !checks
