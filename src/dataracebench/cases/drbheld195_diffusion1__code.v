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

Definition drbheld195_diffusion1٠main : val :=
  vfun: <> =>
    let: "c" := 1 in
    let: "n" := 10 in
    let: "nsteps" := 10 in
    let: "u1" := ref (array٠make "n" 0) in
    let: "u2" := ref (array٠make "n" 0) in
    for: "i" := 1 to "n" - 2 + 1 begin
      array٠set !"u1" "i" 1 ;;
      array٠set !"u2" "i" (array٠get !"u1" "i")
    end ;;
    array٠set !"u1" 0 1 ;;
    array٠set !"u1" ("n" - 1) 1 ;;
    array٠set !"u2" 0 1 ;;
    array٠set !"u2" ("n" - 1) 1 ;;
    for: "_t" := 0 to "nsteps" begin
      drb٠parallel_for
        ("n" - 2)
        (fun: "k" =>
           let: "i" := "k" + 1 in
           array٠set
             !"u2"
             "i"
             (array٠get !"u1" "i"
              +
              "c"
              *
              (array٠get !"u1" ("i" - 1) + array٠get !"u1" ("i" + 1)
               -
               2 * array٠get !"u1" "i"))) ;;
      let: "_tmp" := !"u1" in
      "u1" <- !"u2"
    end.
