From mizzle.lang Require Import
  prelude.
From mizzle.lang Require Import
  instances.
From mizzle Require Import
  drb_axiom.
From mizzle.stdlib Require Import
  mutex.
From mizzle.lang Require Import
  options.

Definition drbheld201_sync1٠main : val :=
  vfun: <> =>
    let: "x" := ref 1 in
    let: "l" := mutex٠create () in
    drb٠par
      (fun: <> => mutex٠lock "l" ;;
                  "x" <- 0 ;;
                  mutex٠unlock "l")
      (fun: <> => mutex٠lock "l" ;;
                  mutex٠unlock "l" ;;
                  "x" <- 1).
