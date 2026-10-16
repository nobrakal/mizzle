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

Definition drb015_outofbounds_var٠main : val :=
  vfun: <> =>
    let: "len" := 100 in
    let: "n" := "len" in
    let: "m" := "len" in
    let: "b" := array٠make ("n" * "m") 0 in
    drb٠parallel_for
      ("n" - 1)
      (fun: "k" =>
         let: "i" := "k" + 1 in
         for: "j" := 0 to "m" begin
           array٠set
             "b"
             ("i" * "m" + "j")
             (array٠get "b" ("i" * "m" + "j" - 1))
         end).
