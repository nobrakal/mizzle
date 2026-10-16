From mizzle.lang Require Import
  prelude.
From mizzle.lang Require Import
  instances.
From mizzle.stdlib Require Import
  atomic_loc.
From mizzle.lang Require Import
  options.

Notation "'Push'" := (
  in_type "cases.lin005_treiber_stack5.req" 0
)(in custom mizzle_tag
).
Notation "'Pop'" := (
  in_type "cases.lin005_treiber_stack5.req" 1
)(in custom mizzle_tag
).
