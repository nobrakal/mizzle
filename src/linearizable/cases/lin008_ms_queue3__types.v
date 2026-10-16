From mizzle.lang Require Import
  prelude.
From mizzle.lang Require Import
  instances.
From mizzle.stdlib Require Import
  atomic_loc.
From mizzle.lang Require Import
  options.

Notation "'Nil'" := (
  in_type "cases.lin008_ms_queue3.node" 0
)(in custom mizzle_tag
).
Notation "'Next'" := (
  in_type "cases.lin008_ms_queue3.node" 1
)(in custom mizzle_tag
).

Notation "'head'" := (
  in_type "cases.lin008_ms_queue3.t" 0
)(in custom mizzle_proj
).
Notation "'tail'" := (
  in_type "cases.lin008_ms_queue3.t" 1
)(in custom mizzle_proj
).

Notation "'Enq'" := (
  in_type "cases.lin008_ms_queue3.req" 0
)(in custom mizzle_tag
).
Notation "'Deq'" := (
  in_type "cases.lin008_ms_queue3.req" 1
)(in custom mizzle_tag
).
