From mizzle.lang Require Import
  prelude.
From mizzle.lang Require Import
  instances.
From mizzle.stdlib Require Import
  atomic_loc.
From mizzle.linearizable.cases Require Import
  lin010_ms_queue5__types.
From mizzle.lang Require Import
  options.

Definition lin010_ms_queue5٠create : val :=
  vfun: <> =>
    let: "next" := ref §Nil in
    (ref "next", ref "next").

Definition lin010_ms_queue5٠peek_opt : val :=
  vfun: "t" =>
    let: "curr" := !ᵃᵗ"t".<head> in
    match: !ᵃᵗ"curr" with
    | Nil =>
        §None
    | Next "value" <> =>
        ‘Some( "value" )
    end.

Definition lin010_ms_queue5٠pop : val :=
  vrec: "pop" "t" =>
    match: lin010_ms_queue5٠peek_opt "t" with
    | None =>
        §None
    | Some "value" =>
        let: "old_head" := !ᵃᵗ"t".<head> in
        match: !ᵃᵗ"old_head" with
        | Nil =>
            §None
        | Next <> "next" =>
            if: atomic_loc٠cas "t".<head> ⟨contents⟩ "old_head" "next" then (
              ‘Some( "value" )
            ) else (
              "pop" "t"
            )
        end
    end.

Definition lin010_ms_queue5٠fix_tail : val :=
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

Definition lin010_ms_queue5٠find_tail_and_enq : val :=
  vrec: "find_tail_and_enq" "curr_end" "node" =>
    if: ~ atomic_loc٠cas "curr_end" ⟨contents⟩ §Nil "node" then (
      match: !ᵃᵗ"curr_end" with
      | Nil =>
          "find_tail_and_enq" "curr_end" "node"
      | Next <> "n" =>
          "find_tail_and_enq" "n" "node"
      end
    ).

Definition lin010_ms_queue5٠push : val :=
  vfun: "t" "value" =>
    let: "new_tail" := ref §Nil in
    let: "newnode" := ‘Next( "value", "new_tail" ) in
    let: "old_tail" := !ᵃᵗ"t".<tail> in
    if: ~ atomic_loc٠cas "old_tail" ⟨contents⟩ §Nil "newnode" then (
      match: !ᵃᵗ"old_tail" with
      | Nil =>
          lin010_ms_queue5٠find_tail_and_enq "old_tail" "newnode"
      | Next <> "n" =>
          lin010_ms_queue5٠find_tail_and_enq "n" "newnode"
      end
    ) else (
      ()
    ) ;;
    if: ~ atomic_loc٠cas "t".<tail> ⟨contents⟩ "old_tail" "new_tail" then (
      lin010_ms_queue5٠fix_tail "t".<tail> "new_tail"
    ).

Definition lin010_ms_queue5٠op : val :=
  vfun: "t" "req" =>
    match: "req" with
    | Enq "x" =>
        lin010_ms_queue5٠push "t" "x" ;;
        §None
    | Deq =>
        lin010_ms_queue5٠pop "t"
    end.
