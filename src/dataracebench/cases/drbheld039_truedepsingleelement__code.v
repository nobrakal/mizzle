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

Definition drbheld039_truedepsingleelement٠main : val :=
  vfun: <> =>
    let: "len" := 1000 in
    let: "a" := array٠make "len" 0 in
    array٠set "a" 0 2 ;;
    drb٠parallel_for
      "len"
      (fun: "i" => array٠set "a" "i" (array٠get "a" "i" + array٠get "a" 0)).
