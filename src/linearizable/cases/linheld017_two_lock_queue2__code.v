From mizzle.lang Require Import
  prelude.
From mizzle.lang Require Import
  instances.
From mizzle.stdlib Require Import
  mutex.
From mizzle.linearizable.cases Require Import
  linheld017_two_lock_queue2__types.
From mizzle.lang Require Import
  options.

Definition linheld017_two_lock_queue2٠create : val :=
  vfun: <> =>
    let: "cell" := ref §Nil in
    (ref "cell", ref "cell", mutex٠create (), mutex٠create ()).

Definition linheld017_two_lock_queue2٠push : val :=
  vfun: "t" "value" =>
    let: "cell" := ref §Nil in
    mutex٠lock "t".<tail_lock> ;;
    let: "last" := !ᵃᵗ"t".<tail> in
    "last" <-ᵃᵗ ‘Next( "value", "cell" ) ;;
    "t".<tail> <-ᵃᵗ "cell" ;;
    mutex٠unlock "t".<tail_lock>.

Definition linheld017_two_lock_queue2٠pop : val :=
  vfun: "t" =>
    let: "first" := !ᵃᵗ"t".<head> in
    mutex٠lock "t".<head_lock> ;;
    match: !ᵃᵗ"first" with
    | Nil =>
        mutex٠unlock "t".<head_lock> ;;
        §None
    | Next "value" "next" =>
        "t".<head> <-ᵃᵗ "next" ;;
        mutex٠unlock "t".<head_lock> ;;
        ‘Some( "value" )
    end.

Definition linheld017_two_lock_queue2٠op : val :=
  vfun: "t" "req" =>
    match: "req" with
    | Enq "x" =>
        linheld017_two_lock_queue2٠push "t" "x" ;;
        §None
    | Deq =>
        linheld017_two_lock_queue2٠pop "t"
    end.
