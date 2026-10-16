From mizzle.lang Require Import
  prelude.
From mizzle.lang Require Import
  instances.
From mizzle.stdlib Require Import
  atomic_loc.
From mizzle.linearizable.cases Require Import
  lin009_ms_queue4__types.
From mizzle.lang Require Import
  options.

Definition lin009_ms_queue4٠create : val :=
  vfun: <> =>
    let: "next" := ref §Nil in
    (ref "next", ref "next").

Definition lin009_ms_queue4٠pop : val :=
  vrec: "pop" "t" =>
    let: "old_head" := !ᵃᵗ"t".<head> in
    match: !ᵃᵗ"old_head" with
    | Nil =>
        §None
    | Next "value" "next" =>
        if: atomic_loc٠cas "t".<head> ⟨contents⟩ "old_head" "next" then (
          ‘Some( "value" )
        ) else (
          "pop" "t"
        )
    end.

Definition lin009_ms_queue4٠fix_tail : val :=
  vrec: "fix_tail" "tail" "new_tail" =>
    let: "old_tail" := !ᵃᵗ"tail" in
    match: !ᵃᵗ"new_tail" with
    | Nil =>
        if: ~ atomic_loc٠cas "tail" ⟨contents⟩ "old_tail" "new_tail" then (
          "fix_tail" "tail" "new_tail"
        )
    | Next <> <> =>
        ()
    end.

Definition lin009_ms_queue4٠push : val :=
  vfun: "t" "value" =>
    let: "new_tail" := ref §Nil in
    let: "newnode" := ‘Next( "value", "new_tail" ) in
    let: "old_tail" := !ᵃᵗ"t".<tail> in
    atomic_loc٠cas "old_tail" ⟨contents⟩ §Nil "newnode" ;;
    if: ~ atomic_loc٠cas "t".<tail> ⟨contents⟩ "old_tail" "new_tail" then (
      lin009_ms_queue4٠fix_tail "t".<tail> "new_tail"
    ).

Definition lin009_ms_queue4٠op : val :=
  vfun: "t" "req" =>
    match: "req" with
    | Enq "x" =>
        lin009_ms_queue4٠push "t" "x" ;;
        §None
    | Deq =>
        lin009_ms_queue4٠pop "t"
    end.
