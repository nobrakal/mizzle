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

Definition drbheld074_flush٠f1 : val :=
  vfun: "lck" "q" =>
    mutex٠lock "lck" ;;
    "q" <- 1 ;;
    mutex٠unlock "lck".

Definition drbheld074_flush٠main : val :=
  vfun: <> =>
    let: "i" := ref 0 in
    let: "lck" := mutex٠create () in
    let: "sum1" := ref 0 in
    let: "sum2" := ref 0 in
    drb٠par
      (fun: <> => drbheld074_flush٠f1 "lck" "i" ;;
                  "sum1" <- !"sum1" + !"i")
      (fun: <> => drbheld074_flush٠f1 "lck" "i" ;;
                  "sum2" <- !"sum2" + !"i") ;;
    let: "_sum" := !"sum1" + !"sum2" in
    ().
