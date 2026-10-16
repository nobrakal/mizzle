From mizzle.lang Require Import
  prelude.
From mizzle.lang Require Import
  instances.
From mizzle.stdlib Require Import
  mutex.
From mizzle.linearizable.cases Require Import
  linheld019_two_lock_queue4__types.
From mizzle.lang Require Import
  options.

Definition linheld019_two_lock_queue4٠create : val :=
  vfun: <> =>
    let: "cell" := ref §Nil in
    (ref "cell", ref "cell", mutex٠create (), mutex٠create ()).

Definition linheld019_two_lock_queue4٠push : val :=
  vfun: "t" "value" =>
    let: "cell" := ref §Nil in
    mutex٠lock "t".<tail_lock> ;;
    let: "last" := !ᵃᵗ"t".<tail> in
    "last" <-ᵃᵗ ‘Next( "value", "cell" ) ;;
    "t".<tail> <-ᵃᵗ "cell" ;;
    mutex٠unlock "t".<tail_lock>.

Definition linheld019_two_lock_queue4٠advance : val :=
  vfun: "t" =>
    mutex٠lock "t".<head_lock> ;;
    let: "first" := !ᵃᵗ"t".<head> in
    match: !ᵃᵗ"first" with
    | Nil =>
        ()
    | Next <> "next" =>
        "t".<head> <-ᵃᵗ "next"
    end ;;
    mutex٠unlock "t".<head_lock>.

Definition linheld019_two_lock_queue4٠pop : val :=
  vfun: "t" =>
    mutex٠lock "t".<head_lock> ;;
    let: "first" := !ᵃᵗ"t".<head> in
    let: "front" := !ᵃᵗ"first" in
    mutex٠unlock "t".<head_lock> ;;
    match: "front" with
    | Nil =>
        §None
    | Next "value" <> =>
        linheld019_two_lock_queue4٠advance "t" ;;
        ‘Some( "value" )
    end.

Definition linheld019_two_lock_queue4٠op : val :=
  vfun: "t" "req" =>
    match: "req" with
    | Enq "x" =>
        linheld019_two_lock_queue4٠push "t" "x" ;;
        §None
    | Deq =>
        linheld019_two_lock_queue4٠pop "t"
    end.
