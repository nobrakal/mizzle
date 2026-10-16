From mizzle.lang Require Import
  prelude.
From mizzle.lang Require Import
  instances.
From mizzle Require Import
  drb_axiom.
From mizzle.stdlib Require Import
  array.
From mizzle.lang Require Import
  options.

Definition drb018_plusplus٠main : val :=
  vfun: <> =>
    let: "in_len" := 1000 in
    let: "out_len" := ref 0 in
    let: "input" := array٠make "in_len" 0 in
    let: "output" := array٠make "in_len" 0 in
    for: "i" := 0 to "in_len" begin
      array٠set "input" "i" "i"
    end ;;
    drb٠parallel_for
      "in_len"
      (fun: "i" =>
         let: "idx" := !"out_len" in
         "out_len" <- "idx" + 1 ;;
         array٠set "output" "idx" (array٠get "input" "i")).
