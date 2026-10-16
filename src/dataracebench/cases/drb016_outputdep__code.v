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

Definition drb016_outputdep٠main : val :=
  vfun: <> =>
    let: "len" := 100 in
    let: "a" := array٠make "len" 0 in
    let: "x" := ref 10 in
    drb٠parallel_for "len" (fun: "i" => array٠set "a" "i" !"x" ;;
                                        "x" <- "i").
