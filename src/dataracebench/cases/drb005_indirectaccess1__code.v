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

Definition drb005_indirectaccess1٠n : val :=
  180.

Definition drb005_indirectaccess1٠main : val :=
  vfun: <> =>
    let: "index_set" := array٠make drb005_indirectaccess1٠n 0 in
    for: "g" := 0 to 29 + 1 begin
      let: "start" := 521 + 338 * ("g" `quot` 6) + 26 * ("g" `rem` 6) in
      for: "k" := 0 to 5 + 1 begin
        array٠set "index_set" (6 * "g" + "k") ("start" + 2 * "k")
      end
    end ;;
    array٠set "index_set" 53 923 ;;
    let: "base" := array٠make (2013 + 12 + 1) 0 in
    for: "i" := 521 to 2025 + 1 begin
      array٠set "base" "i" "i"
    end ;;
    drb٠parallel_for_chunked
      1
      drb005_indirectaccess1٠n
      (fun: "i" =>
         let: "idx" := array٠get "index_set" "i" in
         array٠set "base" "idx" (array٠get "base" "idx" + 1 + "i") ;;
         array٠set
           "base"
           ("idx" + 12)
           (array٠get "base" ("idx" + 12) + 3 + "i")).
