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

Definition drbheld111_linearmissing٠main : val :=
  vfun: <> =>
    let: "len" := 100 in
    let: "a" := array٠make "len" 0 in
    let: "b" := array٠make "len" 0 in
    let: "c" := array٠make "len" 0 in
    let: "j" := ref 0 in
    for: "i" := 0 to "len" begin
      array٠set "a" "i" "i" ;;
      array٠set "b" "i" "i" ;;
      array٠set "c" "i" "i"
    end ;;
    drb٠parallel_for
      "len"
      (fun: "i" =>
         array٠set
           "c"
           !"j"
           (array٠get "c" !"j" + array٠get "a" "i" * array٠get "b" "i") ;;
         "j" <- !"j" + 1).
