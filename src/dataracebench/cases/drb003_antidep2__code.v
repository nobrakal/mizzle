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

Definition drb003_antidep2٠main : val :=
  vfun: <> =>
    let: "len" := 20 in
    let: "a" := array٠make_matrix "len" "len" 1 in
    drb٠parallel_for
      ("len" - 1)
      (fun: "i" =>
         for: "j" := 0 to "len" begin
           array٠set
             (array٠get "a" "i")
             "j"
             (array٠get (array٠get "a" "i") "j"
              +
              array٠get (array٠get "a" ("i" + 1)) "j")
         end).
