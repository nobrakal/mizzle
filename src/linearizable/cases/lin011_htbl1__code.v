From mizzle.lang Require Import
  prelude.
From mizzle.lang Require Import
  instances.
From mizzle.stdlib Require Import
  atomic_loc.
From mizzle.stdlib Require Import
  array.
From mizzle.linearizable.cases Require Import
  lin011_htbl1__types.
From mizzle.lang Require Import
  options.

Definition lin011_htbl1٠create : val :=
  vfun: <> =>
    array٠init 16 (fun: <> => ref §Nil).

Definition lin011_htbl1٠bucket : val :=
  vfun: "t" "key" =>
    array٠get "t" ("key" `land` 15).

Definition lin011_htbl1٠assoc_mem : val :=
  vrec: "assoc_mem" "key" "b" =>
    match: "b" with
    | Nil =>
        false
    | Cons "k" <> "rest" =>
        "k" == "key" or "assoc_mem" "key" "rest"
    end.

Definition lin011_htbl1٠mem : val :=
  vfun: "t" "key" =>
    let: "b" := lin011_htbl1٠bucket "t" "key" in
    lin011_htbl1٠assoc_mem "key" !ᵃᵗ"b".

Definition lin011_htbl1٠try_add : val :=
  vfun: "t" "key" "value" =>
    let: "b" := lin011_htbl1٠bucket "t" "key" in
    let: "old" := !ᵃᵗ"b" in
    if: lin011_htbl1٠assoc_mem "key" "old" then (
      false
    ) else (
      "b" <-ᵃᵗ ‘Cons( "key", "value", "old" ) ;;
      true
    ).

Definition lin011_htbl1٠remove_list : val :=
  vrec: "remove_list" "key" "b" =>
    match: "b" with
    | Nil =>
        §Nil
    | Cons "k" "v" "rest" =>
        if: "k" == "key" then (
          "rest"
        ) else (
          ‘Cons( "k", "v", "remove_list" "key" "rest" )
        )
    end.

Definition lin011_htbl1٠try_remove : val :=
  vrec: "try_remove" "t" "key" =>
    let: "b" := lin011_htbl1٠bucket "t" "key" in
    let: "old" := !ᵃᵗ"b" in
    if: ~ lin011_htbl1٠assoc_mem "key" "old" then (
      false
    ) else if:
       atomic_loc٠cas
         "b"
         ⟨contents⟩
         "old"
         (lin011_htbl1٠remove_list "key" "old")
     then (
      true
    ) else (
      "try_remove" "t" "key"
    ).

Definition lin011_htbl1٠op : val :=
  vfun: "t" "req" =>
    match: "req" with
    | Add "k" "v" =>
        lin011_htbl1٠try_add "t" "k" "v"
    | Remove "k" =>
        lin011_htbl1٠try_remove "t" "k"
    | Mem "k" =>
        lin011_htbl1٠mem "t" "k"
    end.
