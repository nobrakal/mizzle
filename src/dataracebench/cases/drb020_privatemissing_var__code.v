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

Definition drb020_privatemissing_var٠main : val :=
  vfun: <> =>
    let: "tmp" := ref 0 in
    let: "len" := 100 in
    let: "a" := array٠make "len" 0 in
    for: "i" := 0 to "len" begin
      array٠set "a" "i" "i"
    end ;;
    drb٠parallel_for
      "len"
      (fun: "i" =>
         "tmp" <- array٠get "a" "i" + "i" ;;
         array٠set "a" "i" !"tmp").
