From mizzle.lang Require Import
  prelude.
From mizzle.lang Require Import
  instances.
From mizzle.stdlib Require Import
  atomic_loc
  assert.
From mizzle.stdlib Require Import
  structural_equality.
From mizzle.stdlib Require Import
  domain.
From mizzle.linearizable.cases Require Import
  key_buggy_stack__types.
From mizzle.lang Require Import
  options.

Definition key_buggy_stack٠create : val :=
  vfun: <> =>
    ref [].

Definition key_buggy_stack٠push : val :=
  vrec: "push" "t" "v" =>
    let: "xs" := !ᵃᵗ"t" in
    let: "ys" := "v" :: "xs" in
    if: ~ atomic_loc٠cas "t" ⟨contents⟩ !ᵃᵗ"t" "ys" then (
      "push" "t" "v"
    ).

Definition key_buggy_stack٠pop : val :=
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

Definition key_buggy_stack٠op : val :=
  vfun: "t" "req" =>
    match: "req" with
    | Push "x" =>
        key_buggy_stack٠push "t" "x" ;;
        §None
    | Pop =>
        key_buggy_stack٠pop "t"
    end.

Definition key_buggy_stack٠client : val :=
  vfun: <> =>
    let: "t" := key_buggy_stack٠create () in
    let: "f" "i" :=
      key_buggy_stack٠push "t" "i" ;;
      assert (key_buggy_stack٠pop "t" ≠ §None)
    in
    domain٠spawn (fun: <> => "f" 1) ;;
    "f" 2.
