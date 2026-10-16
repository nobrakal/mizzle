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

Definition drbheld179_threadsensitivity٠main : val :=
  vfun: <> =>
    let: "n" := 100 in
    let: "a" := array٠make "n" 0 in
    drb٠parallel_for
      "n"
      (fun: "i" =>
         array٠set "a" "i" "i" ;;
         if: "i" = 1 then (
           array٠set "a" 0 1
         )).
