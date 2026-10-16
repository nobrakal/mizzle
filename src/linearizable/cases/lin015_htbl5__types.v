From mizzle.lang Require Import
  prelude.
From mizzle.lang Require Import
  instances.
From mizzle.stdlib Require Import
  atomic_loc.
From mizzle.stdlib Require Import
  array.
From mizzle.lang Require Import
  options.

Notation "'Nil'" := (
  in_type "cases.lin015_htbl5.bucket" 0
)(in custom mizzle_tag
).
Notation "'Cons'" := (
  in_type "cases.lin015_htbl5.bucket" 1
)(in custom mizzle_tag
).

Notation "'Add'" := (
  in_type "cases.lin015_htbl5.req" 0
)(in custom mizzle_tag
).
Notation "'Remove'" := (
  in_type "cases.lin015_htbl5.req" 1
)(in custom mizzle_tag
).
Notation "'Mem'" := (
  in_type "cases.lin015_htbl5.req" 2
)(in custom mizzle_tag
).
