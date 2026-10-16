From mizzle.lang Require Import
  prelude.
From mizzle.lang Require Import
  instances.
From mizzle.stdlib Require Import
  atomic_loc.
From mizzle.linearizable.cases Require Import
  linheld023_harris_list4__types.
From mizzle.lang Require Import
  options.

Definition linheld023_harris_list4٠create : val :=
  vfun: <> =>
    ref §Nil.

Definition linheld023_harris_list4٠find_from : val :=
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

Definition linheld023_harris_list4٠find : val :=
  vfun: "t" "key" =>
    linheld023_harris_list4٠find_from "t" "t" "key".

Definition linheld023_harris_list4٠mem : val :=
  vfun: "t" "key" =>
    let: <>, "cur" := linheld023_harris_list4٠find "t" "key" in
    match: "cur" with
    | Cons "k" <> <> =>
        "k" == "key"
    |_ =>
        false
    end.

Definition linheld023_harris_list4٠link : val :=
  vrec: "link" "prev" "cell" "node" =>
    let: "cur" := !ᵃᵗ"prev" in
    "cell" <-ᵃᵗ "cur" ;;
    if: atomic_loc٠cas "prev" ⟨contents⟩ "cur" "node" then (
      true
    ) else (
      "link" "prev" "cell" "node"
    ).

Definition linheld023_harris_list4٠try_add : val :=
  vfun: "t" "key" "value" =>
    let: "prev", "cur" := linheld023_harris_list4٠find "t" "key" in
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
      let: "cell" := ref "cur" in
      let: "node" := ‘Cons( "key", "value", "cell" ) in
      if: atomic_loc٠cas "prev" ⟨contents⟩ "cur" "node" then (
        true
      ) else (
        linheld023_harris_list4٠link "prev" "cell" "node"
      )
    ).

Definition linheld023_harris_list4٠try_remove : val :=
  vrec: "try_remove" "t" "key" =>
    let: "prev", "cur" := linheld023_harris_list4٠find "t" "key" in
    match: "cur" with
    | Cons "k" <> "next" =>
        if: "k" == "key" then (
          match: !ᵃᵗ"next" with
          | Marked <> =>
              "try_remove" "t" "key"
          |_ as "succ" =>
              if:
                atomic_loc٠cas "next" ⟨contents⟩ "succ" ‘Marked( "succ" )
              then (
                atomic_loc٠cas "prev" ⟨contents⟩ "cur" "succ" ;;
                true
              ) else (
                "try_remove" "t" "key"
              )
          end
        ) else (
          false
        )
    |_ =>
        false
    end.

Definition linheld023_harris_list4٠op : val :=
  vfun: "t" "req" =>
    match: "req" with
    | Add "k" "v" =>
        linheld023_harris_list4٠try_add "t" "k" "v"
    | Remove "k" =>
        linheld023_harris_list4٠try_remove "t" "k"
    | Mem "k" =>
        linheld023_harris_list4٠mem "t" "k"
    end.
