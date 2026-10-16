From mizzle.lang Require Import
  prelude.
From mizzle.lang Require Import
  instances.
From mizzle.stdlib Require Import
  atomic_loc.
From mizzle.linearizable.cases Require Import
  lin004_treiber_stack4__types.
From mizzle.lang Require Import
  options.

Definition lin004_treiber_stack4٠create : val :=
  vfun: <> =>
    ref [].

Definition lin004_treiber_stack4٠push : val :=
  vfun: "t" "v" =>
    let: "before" := !ᵃᵗ"t" in
    let: "after" := "v" :: "before" in
    atomic_loc٠cas "t" ⟨contents⟩ "before" "after" ;;
    ().

Definition lin004_treiber_stack4٠pop : val :=
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

Definition lin004_treiber_stack4٠op : val :=
  vfun: "t" "req" =>
    match: "req" with
    | Push "x" =>
        lin004_treiber_stack4٠push "t" "x" ;;
        §None
    | Pop =>
        lin004_treiber_stack4٠pop "t"
    end.
