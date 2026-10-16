From mizzle.lang Require Import
  prelude.
From mizzle.lang Require Import
  instances.
From mizzle Require Import
  drb_axiom.
From mizzle.lang Require Import
  options.

Definition drb009_lastprivatemissing٠main : val :=
  vfun: <> =>
    let: "len" := 10000 in
    let: "x" := ref 0 in
    drb٠parallel_for "len" (fun: "i" => "x" <- "i").
