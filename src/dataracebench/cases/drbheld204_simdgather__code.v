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

Definition drbheld204_simdgather٠main : val :=
  vfun: <> =>
    let: "len" := 20000 in
    let: "a" := array٠make (2 * "len") 0 in
    let: "b" := array٠make "len" 0 in
    for: "i" := 0 to 2 * "len" begin
      array٠set "a" "i" "i"
    end ;;
    for: "i" := 0 to "len" begin
      array٠set "b" "i" ("i" + 1)
    end ;;
    drb٠parallel_for
      "len"
      (fun: "i" =>
         array٠set
           "a"
           ("i" + 64)
           (array٠get "a" ("i" * 2) + array٠get "b" "i")).
