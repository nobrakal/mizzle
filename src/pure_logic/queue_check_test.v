(** * Local test of [is_linearizable_check] over the queue model *********

    Self-contained smoke test: does [vm_compute] reduce
    [is_linearizable_check] over a known non-linearizable queue trace
    to [false]? Independent of [test/hw1_*] so iteration is fast. *)

From stdpp Require Import ssreflect.
From mizzle.lang Require Import semantics.

From mizzle.pure_logic Require Import linear linear_check queue_model.

(** A non-linearizable trace, akin to [expected_buggy_trace] of
    [test/hw1_traced.v]. Real-time forces [Enq(1), Enq(2)] to linearize
    before the first [Deq], but the second [Deq] then has to return [3] from queue state [{2;3}] — front is [2], not [3]. *)

Definition test_buggy_trace : list (positive * trace) := [
  (1%positive, Call (‘QEnq( ValInt 1 ))%V) ;
  (2%positive, Call (‘QEnq( ValInt 2 ))%V) ;
  (2%positive, Ret ValUnit) ;
  (1%positive, Ret ValUnit) ;
  (3%positive, Call (§QDeq)%V) ;
  (3%positive, Ret (ValInt 1)) ;
  (4%positive, Call (‘QEnq( ValInt 3 ))%V) ;
  (4%positive, Ret ValUnit) ;
  (5%positive, Call (§QDeq)%V) ;
  (5%positive, Ret (ValInt 3))
].

(** [vm_compute] reduces the check (with the queue's [executable_model])
    to [false] — confirming the architecture works end-to-end. *)
Example test_buggy_trace_check :
  is_linearizable_check test_buggy_trace = false.
Proof. by vm_compute. Qed.

(** Plug into [is_linearizable_check_sound] for the Prop-level result. *)
Example test_buggy_trace_complete : per_tag_complete test_buggy_trace.
Proof.
  intros τ.
  destruct (decide (τ = 1%positive)); subst.
  { exists (‘QEnq(ValInt 1))%V, ValUnit. right. vm_compute. reflexivity. }
  destruct (decide (τ = 2%positive)); subst.
  { exists (‘QEnq(ValInt 2))%V, ValUnit. right. vm_compute. reflexivity. }
  destruct (decide (τ = 3%positive)); subst.
  { exists (§QDeq)%V, (ValInt 1). right. vm_compute. reflexivity. }
  destruct (decide (τ = 4%positive)); subst.
  { exists (‘QEnq(ValInt 3))%V, ValUnit. right. vm_compute. reflexivity. }
  destruct (decide (τ = 5%positive)); subst.
  { exists (§QDeq)%V, (ValInt 3). right. vm_compute. reflexivity. }
  exists ()%V, ()%V. left.
  unfold test_buggy_trace.
  repeat (rewrite filter_cons_False; [|cbn; intros ?; subst; done]).
  apply filter_nil.
Qed.

Theorem test_buggy_trace_not_linearizable :
  ¬ trace_linearizable test_buggy_trace.
Proof.
  apply is_linearizable_check_sound.
  - exact test_buggy_trace_complete.
  - by vm_compute.
Qed.
