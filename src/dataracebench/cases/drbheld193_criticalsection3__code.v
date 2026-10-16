From mizzle.lang Require Import
  prelude.
From mizzle.lang Require Import
  instances.
From mizzle Require Import
  drb_axiom.
From mizzle.stdlib Require Import
  structural_equality.
From mizzle.stdlib Require Import
  mutex.
From mizzle.lang Require Import
  options.

Definition drbheld193_criticalsection3٠main : val :=
  vfun: <> =>
    let: "x" := ref 0 in
    let: "s" := ref 0 in
    let: "a" := mutex٠create () in
    let: "b" := mutex٠create () in
    drb٠par
      (fun: <> => "x" <- 1 ;;
                  mutex٠lock "a" ;;
                  "s" <- 1 ;;
                  mutex٠unlock "a")
      (fun: <> =>
         let: "fin" := ref false in
         while: ~ !"fin" begin
           mutex٠lock "b" ;;
           if: !"s" ≠ 0 then (
             "fin" <- true
           ) else (
             ()
           ) ;;
           mutex٠unlock "b"
         end ;;
         "x" <- 2).
