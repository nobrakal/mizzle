From mizzle.lang Require Import
  prelude.
From mizzle.lang Require Import
  instances.
From mizzle.stdlib Require Import
  atomic_loc.
From mizzle.linearizable.cases Require Import
  linheld022_harris_list3__types.
From mizzle.lang Require Import
  options.

Definition linheld022_harris_list3٠create : val :=
  vfun: <> =>
    ref §Nil.

Definition linheld022_harris_list3٠find_from : val :=
  vrec: "find_from" "t" "prev" "key" =>
    let: "cur" := !ᵃᵗ"prev" in
    match: "cur" with
    | Marked <> =>
        "find_from" "t" "t" "key"
    | Nil =>
        ("prev", "cur")
    | Cons "k" <> "next" =>
        match: !ᵃᵗ"next" with
        | Marked "succ" =>
            if: atomic_loc٠cas "prev" ⟨contents⟩ "cur" "succ" then (
              "find_from" "t" "prev" "key"
            ) else (
              "find_from" "t" "t" "key"
            )
        |_ =>
            if: "k" < "key" then (
              "find_from" "t" "next" "key"
            ) else (
              ("prev", "cur")
            )
        end
    end.

Definition linheld022_harris_list3٠find : val :=
  vfun: "t" "key" =>
    linheld022_harris_list3٠find_from "t" "t" "key".

Definition linheld022_harris_list3٠mem : val :=
  vfun: "t" "key" =>
    let: <>, "cur" := linheld022_harris_list3٠find "t" "key" in
    match: "cur" with
    | Cons "k" <> <> =>
        "k" == "key"
    |_ =>
        false
    end.

Definition linheld022_harris_list3٠try_add : val :=
  vrec: "try_add" "t" "key" "value" =>
    let: "prev", "cur" := linheld022_harris_list3٠find "t" "key" in
    let: "present" :=
      match: "cur" with
      | Cons "k" <> <> =>
          "k" == "key"
      |_ =>
          false
      end
    in
    if: "present" then (
      false
    ) else (
      let: "node" := ‘Cons( "key", "value", ref "cur" ) in
      if: atomic_loc٠cas "prev" ⟨contents⟩ "cur" "node" then (
        true
      ) else (
        "try_add" "t" "key" "value"
      )
    ).

Definition linheld022_harris_list3٠try_remove : val :=
  vrec: "try_remove" "t" "key" =>
    let: "prev", "cur" := linheld022_harris_list3٠find "t" "key" in
    match: "cur" with
    | Cons "k" <> "next" =>
        if: "k" == "key" then (
          match: !ᵃᵗ"next" with
          | Marked <> =>
              "try_remove" "t" "key"
          |_ as "succ" =>
              atomic_loc٠cas "next" ⟨contents⟩ "succ" ‘Marked( "succ" ) ;;
              atomic_loc٠cas "prev" ⟨contents⟩ "cur" "succ" ;;
              true
          end
        ) else (
          false
        )
    |_ =>
        false
    end.

Definition linheld022_harris_list3٠op : val :=
  vfun: "t" "req" =>
    match: "req" with
    | Add "k" "v" =>
        linheld022_harris_list3٠try_add "t" "k" "v"
    | Remove "k" =>
        linheld022_harris_list3٠try_remove "t" "k"
    | Mem "k" =>
        linheld022_harris_list3٠mem "t" "k"
    end.
