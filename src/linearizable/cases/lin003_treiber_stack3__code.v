From mizzle.lang Require Import
  prelude.
From mizzle.lang Require Import
  instances.
From mizzle.stdlib Require Import
  atomic_loc.
From mizzle.linearizable.cases Require Import
  lin003_treiber_stack3__types.
From mizzle.lang Require Import
  options.

Definition lin003_treiber_stack3٠create : val :=
  vfun: <> =>
    ref [].

Definition lin003_treiber_stack3٠push : val :=
  vrec: "push" "t" "v" =>
    let: "after" := "v" :: !ᵃᵗ"t" in
    if: ~ atomic_loc٠cas "t" ⟨contents⟩ !ᵃᵗ"t" "after" then (
      "push" "t" "v"
    ).

Definition lin003_treiber_stack3٠pop : val :=
  vrec: "pop" "t" =>
    match: !ᵃᵗ"t" with
    | [] =>
        §None
    | "hd" :: "tail" as "before" =>
        if: atomic_loc٠cas "t" ⟨contents⟩ "before" "tail" then (
          ‘Some( "hd" )
        ) else (
          "pop" "t"
        )
    end.

Definition lin003_treiber_stack3٠op : val :=
  vfun: "t" "req" =>
    match: "req" with
    | Push "x" =>
        lin003_treiber_stack3٠push "t" "x" ;;
        §None
    | Pop =>
        lin003_treiber_stack3٠pop "t"
    end.
