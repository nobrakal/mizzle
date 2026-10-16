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

Definition drbheld169_missingsyncwrite٠main : val :=
  vfun: <> =>
    let: "n" := 8 in
    let: "r1" := array٠make "n" 0 in
    let: "r" := array٠make ("n" * "n" * "n") 0 in
    for: "i" := 0 to "n" begin
      for: "j" := 0 to "n" begin
        for: "k" := 0 to "n" begin
          array٠set "r" (("i" * "n" + "j") * "n" + "k") "i"
        end
      end
    end ;;
    drb٠parallel_for
      ("n" - 2)
      (fun: "p" =>
         let: "i" := "p" + 1 in
         for: "j" := 1 to "n" - 2 + 1 begin
           for: "k" := 0 to "n" begin
             array٠set
               "r1"
               "k"
               (array٠get "r" (("i" * "n" + ("j" - 1)) * "n" + "k")
                +
                array٠get "r" (("i" * "n" + ("j" + 1)) * "n" + "k")
                +
                array٠get "r" ((("i" - 1) * "n" + "j") * "n" + "k")
                +
                array٠get "r" ((("i" + 1) * "n" + "j") * "n" + "k"))
           end
         end).
