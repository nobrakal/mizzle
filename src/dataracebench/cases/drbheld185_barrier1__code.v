From mizzle.lang Require Import
  prelude.
From mizzle.lang Require Import
  instances.
From mizzle Require Import
  drb_axiom.
From mizzle.stdlib Require Import
  assert.
From mizzle.stdlib Require Import
  structural_equality.
From mizzle.stdlib Require Import
  mutex.
From mizzle.lang Require Import
  options.

Definition drbheld185_barrier1٠raise : val :=
  vfun: "c" "f" =>
    mutex٠lock "c" ;;
    assert (~ !"f") ;;
    "f" <- true ;;
    mutex٠unlock "c".

Definition drbheld185_barrier1٠lower : val :=
  vfun: "c" "f" =>
    let: "fin" := ref false in
    while: ~ !"fin" begin
      mutex٠lock "c" ;;
      if: !"f" then (
        "f" <- false ;;
        "fin" <- true
      ) else (
        ()
      ) ;;
      mutex٠unlock "c"
    end.

Definition drbheld185_barrier1٠mybarrier : val :=
  vfun: "c" "f0" "f1" "tid" =>
    if: "tid" = 0 then (
      drbheld185_barrier1٠raise "c" "f0" ;;
      drbheld185_barrier1٠lower "c" "f0"
    ) else if: "tid" = 1 then (
      drbheld185_barrier1٠raise "c" "f1" ;;
      drbheld185_barrier1٠lower "c" "f1"
    ).

Definition drbheld185_barrier1٠main : val :=
  vfun: <> =>
    let: "n" := 2 in
    let: "x" := ref 1 in
    let: "f0" := ref false in
    let: "f1" := ref false in
    let: "c" := mutex٠create () in
    let: "body" "tid" :=
      for: "_i" := 0 to "n" begin
        drbheld185_barrier1٠mybarrier "c" "f0" "f1" "tid" ;;
        if: "tid" = 0 then (
          "x" <- 0
        ) else (
          ()
        ) ;;
        drbheld185_barrier1٠mybarrier "c" "f0" "f1" "tid" ;;
        drbheld185_barrier1٠mybarrier "c" "f0" "f1" "tid" ;;
        if: "tid" = 1 then (
          "x" <- 1
        ) else (
          ()
        ) ;;
        drbheld185_barrier1٠mybarrier "c" "f0" "f1" "tid"
      end
    in
    drb٠par (fun: <> => "body" 0) (fun: <> => "body" 1).
