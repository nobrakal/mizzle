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

Definition drbheld187_barrier2٠main : val :=
  vfun: <> =>
    let: "x" := ref 1 in
    let: "l0" := mutex٠create () in
    let: "l1" := mutex٠create () in
    drb٠par (fun: <> => mutex٠lock "l0") (fun: <> => mutex٠lock "l1") ;;
    drb٠par
      (fun: <> => "x" <- 0 ;;
                  mutex٠unlock "l0" ;;
                  mutex٠lock "l0")
      (fun: <> => mutex٠unlock "l1" ;;
                  mutex٠lock "l1" ;;
                  "x" <- 1) ;;
    drb٠par (fun: <> => mutex٠unlock "l1") (fun: <> => mutex٠unlock "l0").
