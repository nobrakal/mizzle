From mizzle.lang Require Import
  prelude.
From mizzle.lang Require Import
  instances.
From mizzle Require Import
  drb_axiom.
From mizzle.lang Require Import
  options.

Definition drbheld124_master٠main : val :=
  vfun: <> =>
    let: "init" := ref 0 in
    drb٠par
      (fun: <> => let: "_local" := !"init" in
                  ())
      (fun: <> => "init" <- 10 ;;
                  let: "_local" := !"init" in
                  ()).
