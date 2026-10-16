From mizzle.lang Require Import
  prelude.
From mizzle.lang Require Import
  instances.
From mizzle.stdlib Require Import
  atomic_loc.
From mizzle.linearizable.cases Require Import
  lin001_treiber_stack1__types.
From mizzle.lang Require Import
  options.

Definition lin001_treiber_stack1٠create : val :=
  vfun: <> =>
    ref [].

Definition lin001_treiber_stack1٠push : val :=
  vfun: "t" "v" =>
    "t" <-ᵃᵗ "v" :: !ᵃᵗ"t".

Definition lin001_treiber_stack1٠pop : val :=
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

Definition lin001_treiber_stack1٠op : val :=
  vfun: "t" "req" =>
    match: "req" with
    | Push "x" =>
        lin001_treiber_stack1٠push "t" "x" ;;
        §None
    | Pop =>
        lin001_treiber_stack1٠pop "t"
    end.
