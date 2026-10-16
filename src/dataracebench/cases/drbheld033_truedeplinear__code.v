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

Definition drbheld033_truedeplinear٠main : val :=
  vfun: <> =>
    let: "len" := 2000 in
    let: "a" := array٠make "len" 0 in
    for: "i" := 0 to "len" begin
      array٠set "a" "i" "i"
    end ;;
    drb٠parallel_for
      1000
      (fun: "i" => array٠set "a" (2 * "i" + 1) (array٠get "a" "i" + 1)).
