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

Definition drbheld197_diffusion2٠main : val :=
  vfun: <> =>
    let: "c" := 1 in
    let: "n" := 20 in
    let: "nsteps" := 100 in
    let: "b" := array٠make (2 * "n") 0 in
    let: "u" := array٠make 2 0 in
    array٠set "u" 1 ("n" - 2) ;;
    for: "i" := 1 to "n" - 2 + 1 begin
      array٠set "b" (array٠get "u" 1 + "i") 1 ;;
      array٠set "b" (array٠get "u" 0 + "i") 1
    end ;;
    array٠set "b" (array٠get "u" 0) 1 ;;
    array٠set "b" (array٠get "u" 0 + "n" - 1) 1 ;;
    array٠set "b" (array٠get "u" 1) 1 ;;
    array٠set "b" (array٠get "u" 1 + "n" - 1) 1 ;;
    let: "p" := ref 0 in
    for: "_t" := 0 to "nsteps" begin
      drb٠parallel_for
        ("n" - 2)
        (fun: "k" =>
           let: "i" := "k" + 1 in
           array٠set
             "b"
             (array٠get "u" (1 - !"p") + "i")
             (array٠get "b" (array٠get "u" !"p" + "i")
              +
              "c"
              *
              (array٠get "b" (array٠get "u" !"p" + "i" - 1)
               +
               array٠get "b" (array٠get "u" !"p" + "i" + 1)
               -
               2 * array٠get "b" (array٠get "u" !"p" + "i")))) ;;
      "p" <- 1 - !"p"
    end.
