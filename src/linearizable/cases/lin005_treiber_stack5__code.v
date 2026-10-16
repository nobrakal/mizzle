From mizzle.lang Require Import
  prelude.
From mizzle.lang Require Import
  instances.
From mizzle.stdlib Require Import
  atomic_loc.
From mizzle.linearizable.cases Require Import
  lin005_treiber_stack5__types.
From mizzle.lang Require Import
  options.

Definition lin005_treiber_stack5٠create : val :=
  vfun: <> =>
    ref [].

Definition lin005_treiber_stack5٠push : val :=
  vrec: "push" "t" "v" =>
    let: "before" := !ᵃᵗ"t" in
    let: "after" := "v" :: "before" in
    if: ~ atomic_loc٠cas "t" ⟨contents⟩ "before" "after" then (
      "push" "t" "v"
    ).

Definition lin005_treiber_stack5٠pop : val :=
  vfun: "t" =>
    match: !ᵃᵗ"t" with
    | [] =>
        §None
    | "hd" :: "tail" as "before" =>
        if: atomic_loc٠cas "t" ⟨contents⟩ "before" "tail" then (
          ‘Some( "hd" )
        ) else (
          §None
        )
    end.

Definition lin005_treiber_stack5٠op : val :=
  vfun: "t" "req" =>
    match: "req" with
    | Push "x" =>
        lin005_treiber_stack5٠push "t" "x" ;;
        §None
    | Pop =>
        lin005_treiber_stack5٠pop "t"
    end.
