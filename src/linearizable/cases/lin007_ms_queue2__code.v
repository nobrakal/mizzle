From mizzle.lang Require Import
  prelude.
From mizzle.lang Require Import
  instances.
From mizzle.stdlib Require Import
  atomic_loc.
From mizzle.linearizable.cases Require Import
  lin007_ms_queue2__types.
From mizzle.lang Require Import
  options.

Definition lin007_ms_queue2٠create : val :=
  vfun: <> =>
    let: "next" := ref §Nil in
    (ref "next", ref "next").

Definition lin007_ms_queue2٠pop : val :=
  vfun: "t" =>
    let: "old_head" := !ᵃᵗ"t".<head> in
    match: !ᵃᵗ"old_head" with
    | Nil =>
        §None
    | Next "value" "next" =>
        "t".<head> <-ᵃᵗ "next" ;;
        ‘Some( "value" )
    end.

Definition lin007_ms_queue2٠fix_tail : val :=
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

Definition lin007_ms_queue2٠find_tail_and_enq : val :=
  vrec: "find_tail_and_enq" "curr_end" "node" =>
    if: ~ atomic_loc٠cas "curr_end" ⟨contents⟩ §Nil "node" then (
      match: !ᵃᵗ"curr_end" with
      | Nil =>
          "find_tail_and_enq" "curr_end" "node"
      | Next <> "n" =>
          "find_tail_and_enq" "n" "node"
      end
    ).

Definition lin007_ms_queue2٠push : val :=
  vfun: "t" "value" =>
    let: "new_tail" := ref §Nil in
    let: "newnode" := ‘Next( "value", "new_tail" ) in
    let: "old_tail" := !ᵃᵗ"t".<tail> in
    if: ~ atomic_loc٠cas "old_tail" ⟨contents⟩ §Nil "newnode" then (
      match: !ᵃᵗ"old_tail" with
      | Nil =>
          lin007_ms_queue2٠find_tail_and_enq "old_tail" "newnode"
      | Next <> "n" =>
          lin007_ms_queue2٠find_tail_and_enq "n" "newnode"
      end
    ) else (
      ()
    ) ;;
    if: ~ atomic_loc٠cas "t".<tail> ⟨contents⟩ "old_tail" "new_tail" then (
      lin007_ms_queue2٠fix_tail "t".<tail> "new_tail"
    ).

Definition lin007_ms_queue2٠op : val :=
  vfun: "t" "req" =>
    match: "req" with
    | Enq "x" =>
        lin007_ms_queue2٠push "t" "x" ;;
        §None
    | Deq =>
        lin007_ms_queue2٠pop "t"
    end.
