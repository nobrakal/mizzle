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

Definition drbheld189_barrier3٠barrier_start : val :=
  vfun: "l0" "l1" "l2" "tid" =>
    if: "tid" = 0 then (
      mutex٠lock "l0" ;;
      mutex٠lock "l2"
    ) else if: "tid" = 1 then (
      mutex٠lock "l1"
    ).

Definition drbheld189_barrier3٠barrier_stop : val :=
  vfun: "l0" "l1" "l2" "tid" =>
    if: "tid" = 0 then (
      mutex٠unlock "l0" ;;
      mutex٠unlock "l2"
    ) else if: "tid" = 1 then (
      mutex٠unlock "l1"
    ).

Definition drbheld189_barrier3٠barrier_wait : val :=
  vfun: "l0" "l1" "tid" =>
    if: "tid" = 0 then (
      mutex٠unlock "l0" ;;
      mutex٠lock "l1" ;;
      mutex٠lock "l0" ;;
      mutex٠unlock "l1"
    ) else if: "tid" = 1 then (
      mutex٠lock "l0" ;;
      mutex٠unlock "l1" ;;
      mutex٠unlock "l0" ;;
      mutex٠lock "l1"
    ).

Definition drbheld189_barrier3٠main : val :=
  vfun: <> =>
    let: "n" := 2 in
    let: "x" := ref 1 in
    let: "l0" := mutex٠create () in
    let: "l1" := mutex٠create () in
    let: "l2" := mutex٠create () in
    drb٠par
      (fun: <> => drbheld189_barrier3٠barrier_start "l0" "l1" "l2" 0)
      (fun: <> => drbheld189_barrier3٠barrier_start "l0" "l1" "l2" 1) ;;
    let: "body" "tid" :=
      for: "_i" := 0 to "n" begin
        drbheld189_barrier3٠barrier_wait "l0" "l1" "tid" ;;
        if: "tid" = 0 then (
          "x" <- 0
        ) else (
          ()
        ) ;;
        drbheld189_barrier3٠barrier_wait "l0" "l1" "tid" ;;
        drbheld189_barrier3٠barrier_wait "l0" "l1" "tid" ;;
        if: "tid" = 1 then (
          "x" <- 1
        ) else (
          ()
        ) ;;
        drbheld189_barrier3٠barrier_wait "l0" "l1" "tid"
      end
    in
    drb٠par (fun: <> => "body" 0) (fun: <> => "body" 1) ;;
    drb٠par
      (fun: <> => drbheld189_barrier3٠barrier_stop "l0" "l1" "l2" 0)
      (fun: <> => drbheld189_barrier3٠barrier_stop "l0" "l1" "l2" 1).
