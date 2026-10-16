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

Definition drbheld119_nestlock٠incr_a : val :=
  vfun: "a" =>
    "a" <- !"a" + 1.

Definition drbheld119_nestlock٠incr_b : val :=
  vfun: "b" =>
    "b" <- !"b" + 1.

Definition drbheld119_nestlock٠main : val :=
  vfun: <> =>
    let: "a" := ref 0 in
    let: "b" := ref 0 in
    let: "lck" := mutex٠create () in
    drb٠par
      (fun: <> =>
         mutex٠lock "lck" ;;
         drbheld119_nestlock٠incr_b "b" ;;
         drbheld119_nestlock٠incr_a "a" ;;
         mutex٠unlock "lck")
      (fun: <> => drbheld119_nestlock٠incr_b "b").
