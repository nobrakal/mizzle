From mizzle.test Require Import test_prelude.

From mizzle.stdlib Require Import assert trace.
From mizzle.test Require Import hw1.

(** ** Trace-based variant *********************************************

    Instead of asserting on the dequeued value (which the previous client
    needed a [done] flag to make linearizability-witnessing), we record
    a sequence of events into a [trace] using the [stdlib.trace] library,
    then assert at the end that the recorded trace equals a specific
    non-linearizable trace produced by the lost-update interleaving.

    Each event is a pair [(kind, arg)] of integer literals; the kind is
    one of [CALL_ENQ] / [RET_ENQ] / [CALL_DEQ] / [RET_DEQ]. *)

Definition CALL_ENQ : Z := 0.
Definition RET_ENQ  : Z := 1.
Definition CALL_DEQ : Z := 2.
Definition RET_DEQ  : Z := 3.

(** Wrappers around [enqueue]/[dequeue] that emit call/ret events into
    a trace, so the client doesn't have to manage trace ids by hand. *)

Definition enqueue_traced : val := vfun: "tr" "q" "x" =>
  let: "id" := trace_fresh "tr" (#CALL_ENQ, "x") in
  enqueue "q" "x" ;;
  trace_emit "tr" "id" (#RET_ENQ, 0).

Definition dequeue_traced : val := vfun: "tr" "q" =>
  let: "id" := trace_fresh "tr" (#CALL_DEQ, 0) in
  let: "v"  := dequeue "q" in
  trace_emit "tr" "id" (#RET_DEQ, "v") ;;
  "v".

Definition expected_buggy_trace : list (positive * val) := [
  (5%positive, (ValInt RET_DEQ,  ValInt 3)%V);  (* main: ret deq → 3 *)
  (5%positive, (ValInt CALL_DEQ, ValInt 0)%V);  (* main: call deq *)
  (4%positive, (ValInt RET_ENQ,  ValInt 0)%V);  (* main: ret enq 3 *)
  (4%positive, (ValInt CALL_ENQ, ValInt 3)%V);  (* main: call enq 3 *)
  (3%positive, (ValInt RET_DEQ,  ValInt 1)%V);  (* main: ret deq → 1 *)
  (3%positive, (ValInt CALL_DEQ, ValInt 0)%V);  (* main: call deq *)
  (1%positive, (ValInt RET_ENQ,  ValInt 0)%V);  (* forked: ret enq 1 *)
  (2%positive, (ValInt RET_ENQ,  ValInt 0)%V);  (* main: ret enq 2 *)
  (2%positive, (ValInt CALL_ENQ, ValInt 2)%V);  (* main: call enq 2 *)
  (1%positive, (ValInt CALL_ENQ, ValInt 1)%V)   (* forked: call enq 1 *)
].

Definition hw_buggy_traced : expr :=
  let: "q"    := new_queue 3 in
  let: "tr"   := new_trace () in
  let: "done" := ref false in
  Fork (enqueue_traced "tr" "q" 1 ;; "done" <- true) ;;
  enqueue_traced "tr" "q" 2 ;;
  (rec: "wait" <> => if: !"done" then () else ("wait" ())) () ;;
  dequeue_traced "tr" "q" ;;
  enqueue_traced "tr" "q" 3 ;;
  dequeue_traced "tr" "q" ;;
  let: "trace" := trace_lookup "tr" in
  if: trace_eq "trace" (Val (encode_trace expected_buggy_trace))
  then assert: false
  else ().

Section bugs.
Context `{seqlogGS Σ}.

(** ** Helpers for the traced wrappers.

    Each helper proves the wrapper body once with abstract operands,
    so callers never have to step through the inline [(#KIND, arg)]
    [Block] expressions in the wrapper's body. *)

(** [enqueue_traced] prologue: emit the [CALL_ENQ] event with a fresh
    [τ], then drive the inner [enqueue] up to the bounds [if]. The
    [trace_emit (#RET_ENQ, 0)] tuple in the continuation is left as an
    unreduced [Block] expression so it lines up with what beta-reducing
    [enqueue_traced] actually produces. *)
Lemma goal_enqueue_traced_park p ks (size i x : Z) (ar back l_tr : location)
    (ts : list (positive * val)) (τ : positive) :
  τ ∉ ts.*1 →
  is_trace l_tr ts -∗
  back ↦∗ [ValInt i] -∗
  focused p ks
    (enqueue_traced (ValLoc l_tr)
       (ValInt size, ValLoc ar, ValLoc back)%V (ValInt x)) -∗
  (is_trace l_tr ((τ, (ValInt CALL_ENQ, ValInt x)%V) :: ts) -∗
   back ↦∗ [ValInt i] -∗
   focused p ks
     ((if: (ValInt i) < (ValInt size) then (
         SetField NotAtomic (ValLoc ar) (ValInt i) (‘QSome( ValInt x )) ;;
         FAA (ValLoc back).[contents] 1 ;; ()
       ) else (
         diverge ()
       )) ;;
      trace_emit (ValLoc l_tr) (ValInt (Z.pos τ))
        (ValInt RET_ENQ, ValInt 0)) -∗
   goal ⊤) -∗
  goal ⊤.
Proof.
  iIntros (Hfresh) "Htr Hb Hp Hcont".
  rewrite /enqueue_traced.
  g_call3 "Hp".
  g_block "Hp".
  g_focus (trace_fresh _ _) "Hp".
  iApply (goal_trace_fresh_at _ _ _ _ _ _ τ with "Htr Hp"); first done.
  iIntros "Htr Hp". simpl. g_let "Hp".
  g_focus (enqueue _ _) "Hp".
  iApply (goal_enqueue_park with "Hb Hp"). iIntros "Hb Hp". simpl.
  iApply ("Hcont" with "Htr Hb Hp").
Qed.

(** Resume a parked traced enqueue, including the post-enqueue
    [trace_emit] call, when bounds are OK. *)
Lemma goal_enqueue_traced_resume p ks (size i b x : Z)
    (ar back l_tr : location) (vl : val) dqa atag
    (ts : list (positive * val)) (τ : positive) :
  (0 ≤ i < size)%Z →
  is_trace l_tr ts -∗
  ar ↦ₕ{dqa} Header atag (Z.to_nat size) -∗
  (ar +ₗ i) ↦ vl -∗
  back ↦∗ [ValInt b] -∗
  focused p ks
    ((if: (ValInt i) < (ValInt size) then (
        SetField NotAtomic (ValLoc ar) (ValInt i) (‘QSome( ValInt x )) ;;
        FAA (ValLoc back).[contents] 1 ;; ()
      ) else (
        diverge ()
      )) ;;
     trace_emit (ValLoc l_tr) (ValInt (Z.pos τ))
       (ValInt RET_ENQ, ValInt 0)) -∗
  (is_trace l_tr ((τ, (ValInt RET_ENQ, ValInt 0)%V) :: ts) -∗
   ar ↦ₕ{dqa} Header atag (Z.to_nat size) -∗
   (ar +ₗ i) ↦ ‘QSome( ValInt x )%V -∗
   back ↦∗ [ValInt (b + 1)] -∗
   focused p ks (Val ValUnit) -∗ goal ⊤) -∗
  goal ⊤.
Proof.
  iIntros (Hbound) "Htr Hhdr Hi Hb Hp Hcont".
  g_focus (if: _ < _ then _ else _)%E "Hp".
  iApply (goal_enqueue_resume with "Hhdr Hi Hb Hp"); first lia.
  iIntros "Hhdr Hi Hb Hp". simpl. g_let "Hp".
  g_block "Hp".
  iApply (goal_trace_emit _ with "Htr Hp"). iIntros "Htr Hp". simpl.
  iApply ("Hcont" with "Htr Hhdr Hi Hb Hp").
Qed.

(** Full sequential traced enqueue (slot empty, back at [i]). Emits
    both [CALL_ENQ] and [RET_ENQ] events around the inner [enqueue]. *)
Lemma goal_enqueue_traced_full p ks (size i x : Z) (ar back l_tr : location)
    dqa atag (ts : list (positive * val)) (τ : positive) :
  (0 ≤ i < size)%Z →
  τ ∉ ts.*1 →
  is_trace l_tr ts -∗
  ar ↦ₕ{dqa} Header atag (Z.to_nat size) -∗
  (ar +ₗ i) ↦ ValUnit -∗
  back ↦∗ [ValInt i] -∗
  focused p ks
    (enqueue_traced (ValLoc l_tr)
       (ValInt size, ValLoc ar, ValLoc back)%V (ValInt x)) -∗
  (is_trace l_tr
     ((τ, (ValInt RET_ENQ, ValInt 0)%V)
      :: (τ, (ValInt CALL_ENQ, ValInt x)%V) :: ts) -∗
   ar ↦ₕ{dqa} Header atag (Z.to_nat size) -∗
   (ar +ₗ i) ↦ ‘QSome( ValInt x )%V -∗
   back ↦∗ [ValInt (i + 1)] -∗
   focused p ks (Val ValUnit) -∗ goal ⊤) -∗
  goal ⊤.
Proof.
  iIntros (Hbound Hfresh) "Htr Hhdr Hi Hb Hp Hcont".
  iApply (goal_enqueue_traced_park with "Htr Hb Hp"); first done.
  iIntros "Htr Hb Hp".
  iApply (goal_enqueue_traced_resume with "Htr Hhdr Hi Hb Hp"); first lia.
  iIntros "Htr Hhdr Hi Hb Hp".
  iApply ("Hcont" with "Htr Hhdr Hi Hb Hp").
Qed.

(** Full traced dequeue at slot 0 (the [goal_dequeue_at_zero] case),
    wrapped with [CALL_DEQ]/[RET_DEQ] trace events. *)
Lemma goal_dequeue_traced_at_zero p ks (size b w : Z)
    (ar back l_tr : location) dqa atag
    (ts : list (positive * val)) (τ : positive) :
  (1 ≤ b)%Z →
  (b ≤ size)%Z →
  τ ∉ ts.*1 →
  is_trace l_tr ts -∗
  ar ↦ₕ{dqa} Header atag (Z.to_nat size) -∗
  back ↦∗ [ValInt b] -∗
  (ar +ₗ 0) ↦ ‘QSome( ValInt w )%V -∗
  focused p ks
    (dequeue_traced (ValLoc l_tr)
       (ValInt size, ValLoc ar, ValLoc back)%V) -∗
  (is_trace l_tr
     ((τ, (ValInt RET_DEQ, ValInt w)%V)
      :: (τ, (ValInt CALL_DEQ, ValInt 0)%V) :: ts) -∗
   ar ↦ₕ{dqa} Header atag (Z.to_nat size) -∗
   (ar +ₗ 0) ↦ ValUnit -∗
   back ↦∗ [ValInt b] -∗
   focused p ks (Val (ValInt w)) -∗ goal ⊤) -∗
  goal ⊤.
Proof.
  iIntros (Hb1 Hbs Hfresh) "Htr Hhdr Hb Ha Hp Hcont".
  rewrite /dequeue_traced.
  g_call2 "Hp".
  g_block "Hp".
  g_focus (trace_fresh _ _) "Hp".
  iApply (goal_trace_fresh_at _ _ _ _ _ _ τ with "Htr Hp"); first done.
  iIntros "Htr Hp". simpl. g_let "Hp".
  g_focus (dequeue _) "Hp".
  iApply (goal_dequeue_at_zero with "Hhdr Hb Ha Hp"); [done|done|].
  iIntros "Hhdr Ha Hb Hp". simpl. g_let "Hp".
  g_block "Hp".
  g_focus (trace_emit _ _ _) "Hp".
  iApply (goal_trace_emit _ with "Htr Hp"). iIntros "Htr Hp". simpl.
  g_let "Hp".
  iApply ("Hcont" with "Htr Hhdr Ha Hb Hp").
Qed.

(** Full traced dequeue at slot 2 ([goal_dequeue_at_two] case), wrapped
    with [CALL_DEQ]/[RET_DEQ] trace events. *)
Lemma goal_dequeue_traced_at_two p ks (w : Z) (ar back l_tr : location) dqa atag
    (ts : list (positive * val)) (τ : positive) :
  τ ∉ ts.*1 →
  is_trace l_tr ts -∗
  ar ↦ₕ{dqa} Header atag 3 -∗
  back ↦∗ [ValInt 3] -∗
  (ar +ₗ 0) ↦ ValUnit -∗
  (ar +ₗ 1) ↦ ValUnit -∗
  (ar +ₗ 2) ↦ ‘QSome( ValInt w )%V -∗
  focused p ks
    (dequeue_traced (ValLoc l_tr)
       (ValInt 3, ValLoc ar, ValLoc back)%V) -∗
  (is_trace l_tr
     ((τ, (ValInt RET_DEQ, ValInt w)%V)
      :: (τ, (ValInt CALL_DEQ, ValInt 0)%V) :: ts) -∗
   ar ↦ₕ{dqa} Header atag 3 -∗
   (ar +ₗ 0) ↦ ValUnit -∗
   (ar +ₗ 1) ↦ ValUnit -∗
   (ar +ₗ 2) ↦ ValUnit -∗
   back ↦∗ [ValInt 3] -∗
   focused p ks (Val (ValInt w)) -∗ goal ⊤) -∗
  goal ⊤.
Proof.
  iIntros (Hfresh) "Htr Hhdr Hb Ha0 Ha1 Ha2 Hp Hcont".
  rewrite /dequeue_traced.
  g_call2 "Hp".
  g_block "Hp".
  g_focus (trace_fresh _ _) "Hp".
  iApply (goal_trace_fresh_at _ _ _ _ _ _ τ with "Htr Hp"); first done.
  iIntros "Htr Hp". simpl. g_let "Hp".
  g_focus (dequeue _) "Hp".
  iApply (goal_dequeue_at_two _ _ _ _ _ _ _ with "Hhdr Hb Ha0 Ha1 Ha2 Hp").
  iIntros "Hhdr Ha0 Ha1 Ha2 Hb Hp". simpl. g_let "Hp".
  g_block "Hp".
  g_focus (trace_emit _ _ _) "Hp".
  iApply (goal_trace_emit _ with "Htr Hp"). iIntros "Htr Hp". simpl.
  g_let "Hp".
  iApply ("Hcont" with "Htr Hhdr Ha0 Ha1 Ha2 Hb Hp").
Qed.

Lemma hw_buggy_traced_bug p ks :
  remaining is_stuck' -∗
  focused p ks hw_buggy_traced -∗
  goal ⊤.
Proof.
  iIntros "Hrem Hp". rewrite /hw_buggy_traced.
  (* Allocate the size-3 queue (same prologue as [hw_buggy_bug]). *)
  rewrite /new_queue. g_call "Hp".
  g_focus (Alloc _ _) "Hp".
  iApply (goal_alloc _ _ _ _ 3 with "Hp"); first lia.
  iIntros (ar) "Hhdr Har _ Hp". simpl.
  iDestruct "Har" as "(Ha0 & Ha1 & Ha2 & _)".
  g_let "Hp". g_alloc "Hp" "Htmp".
  iRename select (_ ↦∗ [ValInt 0])%I into "Hb".
  g_let "Hp".
  g_block "Hp". g_let "Hp".
  (* [new_trace ()] — empty trace. *)
  g_focus (new_trace _) "Hp".
  iApply (goal_new_trace _ with "Hp").
  iIntros (l_tr) "Htr Hp". simpl.
  g_let "Hp".
  (* [ref false] for [done]. *)
  g_alloc "Hp" "Htmp".
  iRename select (_ ↦∗ [ValBool false])%I into "Hd".
  g_let "Hp".
  (* Fork: forked thread runs [enqueue_traced tr q 1 ;; done <- true]. *)
  g_fork "Hp" "Hf" "Hfloc". g_let "Hp".
  (* Forked: park the inner enqueue with τ=1, emitting [CALL_ENQ 1]. *)
  g_focus (enqueue_traced _ _ _) "Hf".
  iApply (goal_enqueue_traced_park _ _ _ _ _ _ _ _ _ 1%positive
            with "Htr Hb Hf"); first apply not_elem_of_nil.
  iIntros "Htr Hb Hf". simpl.
  (* Main: full traced enqueue 2 at i=0, τ=2. *)
  g_focus (enqueue_traced _ _ _) "Hp".
  iApply (goal_enqueue_traced_full _ _ 3 0 2 _ _ _ _ _ _ 2%positive
            with "Htr Hhdr [Ha0] Hb Hp"); first lia.
  { set_solver. }
  { iExact "Ha0". }
  iIntros "Htr Hhdr Ha0 Hb Hp". simpl.
  (* Resume forked enqueue: ar[0]=‘QSome(2), back=1. Push the trailing
     [;; done <- true] into [ks] so the helper's premise unifies. *)
  iDestruct (focused_bind_l [CtxLet BAnon _] _ [] with "Hf") as "Hf".
  iApply (goal_enqueue_traced_resume _ _ 3 0 1 1 _ _ _ _ _ _ _ 1%positive
            with "Htr Hhdr Ha0 Hb Hf"); first lia.
  iIntros "Htr Hhdr Ha0 Hb Hf". simpl.
  (* Forked: [() ;; done <- true] → [()]. *)
  g_let "Hf". g_set_field "Hf" "Hd".
  (* Drop forked thread (body finished). *)
  g_let "Hp".
  (* Wait loop: [done] reads [true], exit on first iteration. *)
  g_rec "Hp". g_call "Hp".
  g_get_field "Hp" "Hd". g_if_true "Hp".
  g_let "Hp".
  replace (1 + 1)%Z with 2%Z by lia.
  (* First traced dequeue: τ=3, b=2, returns 1 from slot 0. *)
  g_focus (dequeue_traced _ _) "Hp".
  iApply (goal_dequeue_traced_at_zero _ _ 3 2 1 _ _ _ _ _ _ 3%positive
            with "Htr Hhdr Hb [Ha0] Hp"); [lia|lia|..].
  { set_solver. }
  { iExact "Ha0". }
  iIntros "Htr Hhdr Ha0 Hb Hp". simpl.
  g_let "Hp".
  (* Traced enqueue 3 at i=2, τ=4. *)
  g_focus (enqueue_traced _ _ _) "Hp".
  iApply (goal_enqueue_traced_full _ _ 3 2 3 _ _ _ _ _ _ 4%positive
            with "Htr Hhdr [Ha2] Hb Hp"); first lia.
  { set_solver. }
  { iExact "Ha2". }
  iIntros "Htr Hhdr Ha2 Hb Hp". simpl.
  g_let "Hp". replace (2 + 1)%Z with 3%Z by lia.
  (* Second traced dequeue: τ=5, returns 3 from slot 2. *)
  g_focus (dequeue_traced _ _) "Hp".
  iApply (goal_dequeue_traced_at_two _ _ 3 _ _ _ _ _ _ 5%positive
            with "Htr Hhdr Hb Ha0 Ha1 Ha2 Hp"); first set_solver.
  iIntros "Htr Hhdr Ha0 Ha1 Ha2 Hb Hp". simpl.
  g_let "Hp".
  (* [trace_lookup tr] — yields [encode_trace ts]. *)
  g_focus (trace_lookup _) "Hp".
  iApply (goal_trace_lookup _ with "Htr Hp"). iIntros "Htr Hp". simpl.
  g_let "Hp".
  (* [trace_eq trace expected_buggy_trace] — they're equal, so [true]. *)
  g_focus (trace_eq _ _) "Hp".
  iApply (goal_trace_eq _ _ _ expected_buggy_trace expected_buggy_trace
            with "Hp").
  { repeat constructor; eexists _, _; reflexivity. }
  { repeat constructor; eexists _, _; reflexivity. }
  iIntros "Hp".
  rewrite bool_decide_true; last reflexivity.
  iSimpl in "Hp". g_if_true "Hp".
  (* [assert: false] is stuck. *)
  iApply (goal_assert_stuck with "Hrem Hp").
Qed.

End bugs.
