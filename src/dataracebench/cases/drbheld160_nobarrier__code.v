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

Definition drbheld160_nobarrier٠main : val :=
  vfun: <> =>
    let: "n" := 100 in
    let: "m" := 16 in
    let: "a" := 2 in
    let: "b" := array٠make "m" 0 in
    let: "c" := array٠make "m" 2 in
    let: "temp" := array٠make "m" 0 in
    let: "team" "lo" "hi" :=
      for: "_j" := 0 to "n" begin
        for: "i" := "lo" to "hi" + 1 begin
          array٠set "temp" "i" (array٠get "b" "i" + array٠get "c" "i")
        end ;;
        for: "k" := "lo" to "hi" + 1 begin
          let: "i" := "m" - 1 - "k" in
          array٠set "b" "i" (array٠get "temp" "i" * "a")
        end
      end
    in
    drb٠par (fun: <> => "team" 0 7) (fun: <> => "team" 8 15).
