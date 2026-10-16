From mizzle.lang Require Import
  prelude.
From mizzle.lang Require Import
  instances.
From mizzle.stdlib Require Import
  atomic_loc.
From mizzle.stdlib Require Import
  array.
From mizzle.linearizable.cases Require Import
  lin012_htbl2__types.
From mizzle.lang Require Import
  options.

Definition lin012_htbl2٠create : val :=
  vfun: <> =>
    array٠init 16 (fun: <> => ref §Nil).

Definition lin012_htbl2٠bucket : val :=
  vfun: "t" "key" =>
    array٠get "t" ("key" `land` 15).

Definition lin012_htbl2٠assoc_mem : val :=
  vrec: "assoc_mem" "key" "b" =>
    match: "b" with
    | Nil =>
        false
    | Cons "k" <> "rest" =>
        "k" == "key" or "assoc_mem" "key" "rest"
    end.

Definition lin012_htbl2٠mem : val :=
  vfun: "t" "key" =>
    let: "b" := lin012_htbl2٠bucket "t" "key" in
    lin012_htbl2٠assoc_mem "key" !ᵃᵗ"b".

Definition lin012_htbl2٠try_add : val :=
  vrec: "try_add" "t" "key" "value" =>
    let: "b" := lin012_htbl2٠bucket "t" "key" in
    let: "old" := !ᵃᵗ"b" in
    if: lin012_htbl2٠assoc_mem "key" "old" then (
      false
    ) else if:
       atomic_loc٠cas "b" ⟨contents⟩ "old" ‘Cons( "key", "value", "old" )
     then (
      true
    ) else (
      "try_add" "t" "key" "value"
    ).

Definition lin012_htbl2٠remove_list : val :=
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

Definition lin012_htbl2٠try_remove : val :=
  vfun: "t" "key" =>
    let: "b" := lin012_htbl2٠bucket "t" "key" in
    let: "old" := !ᵃᵗ"b" in
    if: ~ lin012_htbl2٠assoc_mem "key" "old" then (
      false
    ) else (
      "b" <-ᵃᵗ lin012_htbl2٠remove_list "key" "old" ;;
      true
    ).

Definition lin012_htbl2٠op : val :=
  vfun: "t" "req" =>
    match: "req" with
    | Add "k" "v" =>
        lin012_htbl2٠try_add "t" "k" "v"
    | Remove "k" =>
        lin012_htbl2٠try_remove "t" "k"
    | Mem "k" =>
        lin012_htbl2٠mem "t" "k"
    end.
