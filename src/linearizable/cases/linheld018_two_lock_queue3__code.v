From mizzle.lang Require Import
  prelude.
From mizzle.lang Require Import
  instances.
From mizzle.stdlib Require Import
  mutex.
From mizzle.linearizable.cases Require Import
  linheld018_two_lock_queue3__types.
From mizzle.lang Require Import
  options.

Definition linheld018_two_lock_queue3٠create : val :=
  vfun: <> =>
    let: "cell" := ref §Nil in
    (ref "cell", ref "cell", mutex٠create (), mutex٠create ()).

Definition linheld018_two_lock_queue3٠push : val :=
  vfun: "t" "value" =>
    let: "cell" := ref §Nil in
    mutex٠lock "t".<tail_lock> ;;
    let: "last" := !ᵃᵗ"t".<tail> in
    "t".<tail> <-ᵃᵗ "cell" ;;
    mutex٠unlock "t".<tail_lock> ;;
    "last" <-ᵃᵗ ‘Next( "value", "cell" ).

Definition linheld018_two_lock_queue3٠pop : val :=
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

Definition linheld018_two_lock_queue3٠op : val :=
  vfun: "t" "req" =>
    match: "req" with
    | Enq "x" =>
        linheld018_two_lock_queue3٠push "t" "x" ;;
        §None
    | Deq =>
        linheld018_two_lock_queue3٠pop "t"
    end.
