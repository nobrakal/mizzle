From mizzle.lang Require Import
  prelude.
From mizzle.lang Require Import
  instances.
From mizzle.stdlib Require Import
  mutex.
From mizzle.linearizable.cases Require Import
  linheld016_two_lock_queue1__types.
From mizzle.lang Require Import
  options.

Definition linheld016_two_lock_queue1٠create : val :=
  vfun: <> =>
    let: "cell" := ref §Nil in
    (ref "cell", ref "cell", mutex٠create (), mutex٠create ()).

Definition linheld016_two_lock_queue1٠push : val :=
  vfun: "t" "value" =>
    let: "cell" := ref §Nil in
    let: "last" := !ᵃᵗ"t".<tail> in
    "last" <-ᵃᵗ ‘Next( "value", "cell" ) ;;
    "t".<tail> <-ᵃᵗ "cell".

Definition linheld016_two_lock_queue1٠pop : val :=
  vfun: "t" =>
    mutex٠lock "t".<head_lock> ;;
    let: "first" := !ᵃᵗ"t".<head> in
    match: !ᵃᵗ"first" with
    | Nil =>
        mutex٠unlock "t".<head_lock> ;;
        §None
    | Next "value" "next" =>
        "t".<head> <-ᵃᵗ "next" ;;
        mutex٠unlock "t".<head_lock> ;;
        ‘Some( "value" )
    end.

Definition linheld016_two_lock_queue1٠op : val :=
  vfun: "t" "req" =>
    match: "req" with
    | Enq "x" =>
        linheld016_two_lock_queue1٠push "t" "x" ;;
        §None
    | Deq =>
        linheld016_two_lock_queue1٠pop "t"
    end.
