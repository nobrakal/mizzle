From mizzle.lang Require Import
  prelude.
From mizzle.lang Require Import
  instances.
From mizzle.stdlib Require Import
  atomic_loc
  assert.
From mizzle.stdlib Require Import
  structural_equality.
From mizzle.stdlib Require Import
  domain.
From mizzle.lang Require Import
  options.

Notation "'Push'" := (
  in_type "cases.key_buggy_stack.req" 0
)(in custom mizzle_tag
).
Notation "'Pop'" := (
  in_type "cases.key_buggy_stack.req" 1
)(in custom mizzle_tag
).
