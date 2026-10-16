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

Definition drbheld037_truedepseconddimension٠main : val :=
  vfun: <> =>
    let: "n" := 1000 in
    let: "m" := 1000 in
    let: "b" := array٠make_matrix "n" "m" 0 in
    for: "i" := 0 to "n" begin
      drb٠parallel_for
        ("m" - 1)
        (fun: "k" =>
           let: "j" := "k" + 1 in
           array٠set
             (array٠get "b" "i")
             "j"
             (array٠get (array٠get "b" "i") ("j" - 1)))
    end.
