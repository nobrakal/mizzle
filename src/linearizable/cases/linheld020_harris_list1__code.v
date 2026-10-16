From mizzle.lang Require Import
  prelude.
From mizzle.lang Require Import
  instances.
From mizzle.stdlib Require Import
  atomic_loc.
From mizzle.linearizable.cases Require Import
  linheld020_harris_list1__types.
From mizzle.lang Require Import
  options.

Definition linheld020_harris_list1٠create : val :=
  vfun: <> =>
    ref §Nil.

Definition linheld020_harris_list1٠find_from : val :=
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

Definition linheld020_harris_list1٠find : val :=
  vfun: "t" "key" =>
    linheld020_harris_list1٠find_from "t" "t" "key".

Definition linheld020_harris_list1٠mem : val :=
  vfun: "t" "key" =>
    let: <>, "cur" := linheld020_harris_list1٠find "t" "key" in
    match: "cur" with
    | Cons "k" <> <> =>
        "k" == "key"
    |_ =>
        false
    end.

Definition linheld020_harris_list1٠try_add : val :=
  vrec: "try_add" "t" "key" "value" =>
    let: "prev", "cur" := linheld020_harris_list1٠find "t" "key" in
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

Definition linheld020_harris_list1٠try_remove : val :=
  vrec: "try_remove" "t" "key" =>
    let: "prev", "cur" := linheld020_harris_list1٠find "t" "key" in
    match: "cur" with
    | Cons "k" <> "next" =>
        if: "k" == "key" then (
          match: !ᵃᵗ"next" with
          | Marked <> =>
              "try_remove" "t" "key"
          |_ as "succ" =>
              if: atomic_loc٠cas "prev" ⟨contents⟩ "cur" "succ" then (
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

Definition linheld020_harris_list1٠op : val :=
  vfun: "t" "req" =>
    match: "req" with
    | Add "k" "v" =>
        linheld020_harris_list1٠try_add "t" "k" "v"
    | Remove "k" =>
        linheld020_harris_list1٠try_remove "t" "k"
    | Mem "k" =>
        linheld020_harris_list1٠mem "t" "k"
    end.
