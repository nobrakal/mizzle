(** ocaml2mizzle-input version of the Treiber stack.

    This is the source fed to [ocaml2mizzle] to produce the Rocq/MizzleLang embedding in
    [../treiber_stack__code.v]. It is a restricted variant of the faithful
    port in [../treiber_stack.ml], because ocaml2mizzle's input language only accepts a
    subset of OCaml. Specifically, relative to the full port we drop:

    - [Backoff]: the backoff is a pure performance optimization (a randomized
      spin between failed CASes) with no effect on behavior; MizzleLang has no
      [Domain.cpu_relax]/[Random.bits] and forbids the computed top-level
      constants the backoff library uses. The retry is a plain tail call here.
    - the [Empty] exception and the [peek_exn]/[pop_exn]/[drop_exn] variants:
      MizzleLang has no exceptions. The option-returning variants are kept.
    - the [poly]/[poly2] GADTs and [peek_as]/[pop_as]: MizzleLang has no GADTs /
      polymorphic recursion. The concrete [*_opt] functions replace them.
    - [push_all]/[add_seq]/[of_seq]/[to_seq]/[of_list]: these need [Seq] or the
      [List.rev_append]/[(@)] helpers, which do not map cleanly onto [mizzle.stdlib].
    - [Atomic.make_contended] becomes [Atomic.make] (contention padding is a
      layout hint, semantically [make]).

    What remains is the heart of the algorithm — the lock-free CAS retry loops —
    translated verbatim. *)

type 'a t = 'a list Atomic.t

let create () =
  Atomic.make []

let is_empty t =
  match Atomic.get t with
  | [] -> true
  | _ :: _ -> false

let peek_opt t =
  match Atomic.get t with
  | [] -> None
  | hd :: _ -> Some hd

let rec push t v =
  let before = Atomic.get t in
  let after = v :: before in
  if not (Atomic.compare_and_set t before after) then
    push t v

let rec pop_opt t =
  match Atomic.get t with
  | [] ->
      None
  | hd :: tail as before ->
      if Atomic.compare_and_set t before tail then
        Some hd
      else
        pop_opt t

let rec pop_all t =
  let before = Atomic.get t in
  if Atomic.compare_and_set t before [] then
    before
  else
    pop_all t
