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

Definition drbheld191_criticalsection2٠main : val :=
  vfun: <> =>
    let: "cap" := 10 in
    let: "size" := ref 0 in
    let: "a" := mutex٠create () in
    let: "b" := mutex٠create () in
    drb٠par
      (fun: <> =>
         let: "r" := ref 0 in
         while: true begin
           mutex٠lock "a" ;;
           if: !"size" < "cap" then (
             "size" <- !"size" + 1
           ) else (
             ()
           ) ;;
           mutex٠unlock "a" ;;
           for: "_i" := 0 to 999 + 1 begin
             "r" <- ((!"r" + 1) `rem` 10)
           end
         end)
      (fun: <> =>
         let: "r" := ref 0 in
         while: true begin
           mutex٠lock "b" ;;
           if: !"size" > 0 then (
             "size" <- !"size" - 1
           ) else (
             ()
           ) ;;
           mutex٠unlock "b" ;;
           for: "_i" := 0 to 999 + 1 begin
             "r" <- ((!"r" + 1) `rem` 10)
           end
         end).
