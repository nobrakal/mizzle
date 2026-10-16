From mizzle.lang Require Import
  prelude.
From mizzle.lang Require Import
  instances.
From mizzle.stdlib Require Import
  mutex.
From mizzle.lang Require Import
  options.

Notation "'Nil'" := (
  in_type "cases.linheld016_two_lock_queue1.node" 0
)(in custom mizzle_tag
).
Notation "'Next'" := (
  in_type "cases.linheld016_two_lock_queue1.node" 1
)(in custom mizzle_tag
).

Notation "'head'" := (
  in_type "cases.linheld016_two_lock_queue1.t" 0
)(in custom mizzle_proj
).
Notation "'tail'" := (
  in_type "cases.linheld016_two_lock_queue1.t" 1
)(in custom mizzle_proj
).
Notation "'head_lock'" := (
  in_type "cases.linheld016_two_lock_queue1.t" 2
)(in custom mizzle_proj
).
Notation "'tail_lock'" := (
  in_type "cases.linheld016_two_lock_queue1.t" 3
)(in custom mizzle_proj
).

Notation "'Enq'" := (
  in_type "cases.linheld016_two_lock_queue1.req" 0
)(in custom mizzle_tag
).
Notation "'Deq'" := (
  in_type "cases.linheld016_two_lock_queue1.req" 1
)(in custom mizzle_tag
).
