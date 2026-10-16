From mizzle.lang Require Import
  prelude.
From mizzle.lang Require Import
  instances.
From mizzle.stdlib Require Import
  atomic_loc.
From mizzle.lang Require Import
  options.

Notation "'Nil'" := (
  in_type "cases.lin010_ms_queue5.node" 0
)(in custom mizzle_tag
).
Notation "'Next'" := (
  in_type "cases.lin010_ms_queue5.node" 1
)(in custom mizzle_tag
).

Notation "'head'" := (
  in_type "cases.lin010_ms_queue5.t" 0
)(in custom mizzle_proj
).
Notation "'tail'" := (
  in_type "cases.lin010_ms_queue5.t" 1
)(in custom mizzle_proj
).

Notation "'Enq'" := (
  in_type "cases.lin010_ms_queue5.req" 0
)(in custom mizzle_tag
).
Notation "'Deq'" := (
  in_type "cases.lin010_ms_queue5.req" 1
)(in custom mizzle_tag
).
