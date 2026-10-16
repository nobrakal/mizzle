From mizzle.lang Require Import
  prelude.
From mizzle.lang Require Import
  instances.
From mizzle.stdlib Require Import
  atomic_loc.
From mizzle.linearizable.cases Require Import
  lin002_treiber_stack2__types.
From mizzle.lang Require Import
  options.

Definition lin002_treiber_stack2٠create : val :=
  vfun: <> =>
    ref [].

Definition lin002_treiber_stack2٠push : val :=
  vrec: "push" "t" "v" =>
    let: "before" := !ᵃᵗ"t" in
    let: "after" := "v" :: "before" in
    if: ~ atomic_loc٠cas "t" ⟨contents⟩ "before" "after" then (
      "push" "t" "v"
    ).

Definition lin002_treiber_stack2٠pop : val :=
  vfun: "t" =>
    match: !ᵃᵗ"t" with
    | [] =>
        §None
    | "hd" :: "tail" =>
        "t" <-ᵃᵗ "tail" ;;
        ‘Some( "hd" )
    end.

Definition lin002_treiber_stack2٠op : val :=
  vfun: "t" "req" =>
    match: "req" with
    | Push "x" =>
        lin002_treiber_stack2٠push "t" "x" ;;
        §None
    | Pop =>
        lin002_treiber_stack2٠pop "t"
    end.
