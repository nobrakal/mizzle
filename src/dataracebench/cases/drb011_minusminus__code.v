From mizzle.lang Require Import
  prelude.
From mizzle.lang Require Import
  instances.
From mizzle Require Import
  drb_axiom.
From mizzle.stdlib Require Import
  structural_equality.
From mizzle.stdlib Require Import
  array.
From mizzle.lang Require Import
  options.

Definition drb011_minusminus٠main : val :=
  vfun: <> =>
    let: "len" := 100 in
    let: "num_nodes" := "len" in
    let: "num_nodes2" := ref 0 in
    let: "x" := array٠make "len" 0 in
    for: "i" := 0 to "len" begin
      if: ("i" `rem` 2) = 0 then (
        array٠set "x" "i" 5
      ) else (
        array٠set "x" "i" (-5)
      )
    end ;;
    drb٠parallel_for
      "num_nodes"
      (fun: "i" =>
         if: array٠get "x" "i" ≤ 0 then (
           "num_nodes2" <- !"num_nodes2" - 1
         )).
