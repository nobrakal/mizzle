From mizzle.test Require Import test_prelude.

From mizzle.stdlib Require Import assert trace.

(** * Queue slot tags *********************************************************
    [§QNone] is a 0-arg block with tag 0, which is the same value as MizzleLang's
    [()] / [ValUnit]. So a freshly-allocated array (whose cells default to
    [ValUnit] — see [goal_alloc]) is equivalent to one filled with [§QNone],
    and we can match on [QNone]/[QSome] over the raw ValUnit cells. *)

Notation "'QNone'" :=
  (in_type "test.hw1.qslot" 0)
  (in custom mizzle_tag).
Notation "'QSome'" :=
  (in_type "test.hw1.qslot" 1)
  (in custom mizzle_tag).
Notation "'QAR'" :=
  (in_type "test.hw1.qar" 0)
  (in custom mizzle_tag).

(** Runtime array load (the field index is an [expr], not a compile-time
    literal). For stores, write [SetField NotAtomic ar i v] explicitly — defining a
    notation for it conflicts with MizzleLang's [e1 <- e2] (ref store) which
    has the same prefix. *)
Notation "e1 .{[ e2 ]}" :=
  (GetField NotAtomic e1%E e2%E)
  (at level 2,
   format "e1 .{[ e2 ]}")
  : expr_scope.

(** ** Helper definitions: [maximum]/[minimum]/[diverge] *)

Definition maximum : val := vfun: "m" "n" =>
  if: "m" ≤ "n" then "n" else "m".

Definition minimum : val := vfun: "m" "n" =>
  if: "m" ≤ "n" then "m" else "n".

Definition diverge : val := vrec: "loop" "v" => "loop" "v".

(** * Implementation of the queue operations ********************************)

Definition new_queue : val :=
  vfun: "sz" =>
    let: "ar"   := Alloc (Val (ValNat (in_type "test.hw1.qar" 0))) "sz" in
    let: "back" := ref 0 in
    ("sz", "ar", "back").

Definition enqueue : val :=
  vfun: "q" "x" =>
    let: "q_size", "q_ar", "q_back" := "q" in
    let: "i" := !"q_back" in
    if: "i" < "q_size" then (
      SetField NotAtomic "q_ar" "i" (‘QSome( "x" )) ;;
      FAA "q_back".[contents] 1 ;; ()
    ) else (
      diverge ()
    ).

Definition dequeue_aux : val :=
  vrec: "loop" "dequeue" "q" "range" "i" =>
    if: "i" == 0 then (
      "dequeue" "q"
    ) else (
      let: "q_size", "q_ar", "q_back" := "q" in
      let: "j" := "range" - "i" in
      let: "x" := "q_ar".{["j"]} in
      match: "x" with
      | QNone     => "loop" "dequeue" "q" "range" ("i" - 1)
      | QSome "v" =>
          (if: CAS ("q_ar", "j") "x" (§QNone) then "v"
           else ("loop" "dequeue" "q" "range" ("i" - 1)))
      end
    ).

Definition dequeue : val :=
  vrec: "dequeue" "q" =>
    let: "q_size", "q_ar", "q_back" := "q" in
    let: "range" := minimum !"q_back" "q_size" in
    dequeue_aux "dequeue" "q" "range" "range".

(** * Buggy test program ****************************************************

    Two concurrent enqueues into a fresh size-3 queue (forked [enqueue 1],
    main [enqueue 2]). The forked thread sets a [done] flag once its
    enqueue returns; main spins on [done] before doing any dequeue. This
    forces a real-time precedence — the forked [enqueue 1] response
    precedes the first dequeue's invocation — so the linearization point
    of [enqueue 1] cannot be deferred past main's later operations.

    In any *linearizable* execution of this client, both enqueues must
    linearize before the first dequeue. The queue then contains [{1, 2}],
    so the first dequeue returns one of them, [enqueue 3] adds [3], and
    the second dequeue must return whichever of [{1, 2}] the first did
    not consume. Hence [y ∈ {1, 2}] and [y < 3] always holds.

    The buggy execution we exhibit: forked thread parks after reading
    [back = 0] but before its store, lets main complete [enqueue 2]
    (so [ar[0] := QSome 2], [back := 1]), then resumes — overwriting
    [ar[0]] with [QSome 1] and advancing [back] to 2 — and finally sets
    [done]. One enqueue's data is silently lost. Main exits the spin,
    dequeues [1] from [ar[0]], enqueues [3] (lands at [ar[2]]), and on
    the second dequeue scans past the empty [ar[0]] and [ar[1]] to
    return [3]. The assertion [y < 3] becomes [3 < 3], i.e. [false],
    and we close via [g_assert_stuck]. *)

Definition hw_buggy : expr :=
  let: "q"    := new_queue 3 in
  let: "done" := ref false in
  Fork (enqueue "q" 1 ;; "done" <- true) ;;
  enqueue "q" 2 ;;
  (rec: "wait" <> => if: !"done" then () else ("wait" ())) () ;;
  dequeue "q" ;;
  enqueue "q" 3 ;;
  let: "y" := dequeue "q" in
  assert: "y" < 3.

Section bugs.
Context `{seqlogGS Σ}.

(** ** Helpers (specs written against the public [enqueue]/[dequeue]
       values; the proofs unfold them locally). *)

Lemma goal_minimum p ks (m n : Z) :
  focused p ks (minimum (ValInt m) (ValInt n)) -∗
  (focused p ks (Val (ValInt (Z.min m n))) -∗ goal ⊤) -∗
  goal ⊤.
Proof.
  iIntros "Hp Hcont". rewrite /minimum.
  g_call2 "Hp". g_binop "Hp".
  destruct (Z.le_gt_cases m n) as [Hle | Hgt].
  - rewrite (bool_decide_eq_true_2 _ Hle). g_if_true "Hp".
    rewrite Z.min_l; [|lia]. iApply ("Hcont" with "Hp").
  - rewrite (bool_decide_eq_false_2 _); [|lia]. g_if_false "Hp".
    rewrite Z.min_r; [|lia]. iApply ("Hcont" with "Hp").
Qed.

(** [enqueue]'s prologue: drive the let bindings and the load on [back],
    parking the thread just before the bounds [if]. The continuation gets
    [back ↦∗ [ValInt i]] (unchanged) and a focused at the parked
    expression parameterised over the loaded index [i]. *)
Lemma goal_enqueue_park p ks (size i : Z) (ar back : location) (x : val) :
  back ↦∗ [ValInt i] -∗
  focused p ks (enqueue (ValInt size, ValLoc ar, ValLoc back)%V x) -∗
  (back ↦∗ [ValInt i] -∗
   focused p ks
     (if: (ValInt i) < (ValInt size) then (
        SetField NotAtomic (ValLoc ar) (ValInt i) (‘QSome( x )) ;;
        FAA (ValLoc back).[contents] 1 ;; ()
      ) else (
        diverge ()
      )) -∗
   goal ⊤) -∗
  goal ⊤.
Proof.
  iIntros "Hb Hp Hcont". rewrite /enqueue.
  g_call2 "Hp".
  g_match "Hp".
  g_get_field "Hp" "Hb". g_let "Hp".
  iApply ("Hcont" with "Hb Hp").
Qed.

(** Resume a parked enqueue when bounds-ok. [vl] is whatever value
    happens to occupy [ar +ₗ i] right now — possibly written by another
    racing enqueue. *)
Lemma goal_enqueue_resume p ks (size i b : Z) (ar back : location) (x vl : val)
    dqa atag :
  (0 ≤ i < size)%Z →
  ar ↦ₕ{dqa} Header atag (Z.to_nat size) -∗
  (ar +ₗ i) ↦ vl -∗
  back ↦∗ [ValInt b] -∗
  focused p ks
    (if: (ValInt i) < (ValInt size) then (
       SetField NotAtomic (ValLoc ar) (ValInt i) (‘QSome( x )) ;;
       FAA (ValLoc back).[contents] 1 ;; ()
     ) else (
       diverge ()
     )) -∗
  (ar ↦ₕ{dqa} Header atag (Z.to_nat size) -∗
   (ar +ₗ i) ↦ ‘QSome( x )%V -∗
   back ↦∗ [ValInt (b + 1)] -∗
   focused p ks (Val ValUnit) -∗ goal ⊤) -∗
  goal ⊤.
Proof.
  iIntros (Hbound) "Hhdr Hi Hb Hp Hcont".
  g_binop "Hp".
  rewrite (bool_decide_eq_true_2 (i < size)%Z); [|lia].
  g_if_true "Hp".
  g_block "Hp".
  g_set_field_cell "Hp" "Hhdr" "Hi". g_let "Hp".
  g_block "Hp".
  g_focus (FAA _ _) "Hp".
  iApply (focused_faa _ _ _ _ 0 with "Hp Hb"); [lia|done|]. iIntros "Hb Hp". simpl.
  g_let "Hp".
  iApply ("Hcont" with "Hhdr Hi Hb Hp").
Qed.

(** Full sequential enqueue when bounds-ok and slot empty. *)
Lemma goal_enqueue_full p ks (size i : Z) (ar back : location) (x : val) dqa atag :
  (0 ≤ i < size)%Z →
  ar ↦ₕ{dqa} Header atag (Z.to_nat size) -∗
  (ar +ₗ i) ↦ ValUnit -∗
  back ↦∗ [ValInt i] -∗
  focused p ks (enqueue (ValInt size, ValLoc ar, ValLoc back)%V x) -∗
  (ar ↦ₕ{dqa} Header atag (Z.to_nat size) -∗
   (ar +ₗ i) ↦ ‘QSome( x )%V -∗
   back ↦∗ [ValInt (i + 1)] -∗
   focused p ks (Val ValUnit) -∗ goal ⊤) -∗
  goal ⊤.
Proof.
  iIntros (Hbound) "Hhdr Hi Hb Hp Hcont".
  iApply (goal_enqueue_park with "Hb Hp"). iIntros "Hb Hp". simpl.
  iApply (goal_enqueue_resume with "Hhdr Hi Hb Hp"); first lia.
  iIntros "Hhdr Hi Hb Hp".
  iApply ("Hcont" with "Hhdr Hi Hb Hp").
Qed.

(** First-slot dequeue: [back] holds [ValInt b] with [b ≥ 1], slot 0
    holds [‘QSome(ValInt w)]. Drives the dequeue to completion, returning
    [ValInt w] and leaving slot 0 empty. *)
Lemma goal_dequeue_at_zero p ks (size b w : Z) (ar back : location) dqa atag :
  (1 ≤ b)%Z →
  (b ≤ size)%Z →
  ar ↦ₕ{dqa} Header atag (Z.to_nat size) -∗
  back ↦∗ [ValInt b] -∗
  (ar +ₗ 0) ↦ ‘QSome( ValInt w )%V -∗
  focused p ks (dequeue (ValInt size, ValLoc ar, ValLoc back)%V) -∗
  (ar ↦ₕ{dqa} Header atag (Z.to_nat size) -∗
   (ar +ₗ 0) ↦ ValUnit -∗
   back ↦∗ [ValInt b] -∗
   focused p ks (Val (ValInt w)) -∗ goal ⊤) -∗
  goal ⊤.
Proof.
  iIntros (Hb1 Hbs) "Hhdr Hb Ha Hp Hcont". rewrite /dequeue.
  g_call "Hp".
  g_match "Hp".
  g_get_field "Hp" "Hb".
  g_focus (minimum _ _) "Hp".
  iApply (goal_minimum with "Hp"). iIntros "Hp". simpl.
  rewrite Z.min_l; [|lia]. g_let "Hp".
  rewrite /dequeue_aux. g_call4 "Hp".
  g_equal "Hp".
  rewrite (bool_decide_eq_false_2 (b = 0)); [|lia].
  g_if_false "Hp".
  g_match "Hp".
  g_binop "Hp".
  replace (b - b)%Z with 0%Z by lia.
  g_let "Hp".
  g_get_field_cell "Hp" "Hhdr" "Ha". g_let "Hp".
  g_match "Hp".
  g_block "Hp".
  g_focus (CAS _ _ _) "Hp".
  iApply (focused_cas_succ_cell with "Hp Hhdr Ha"); [reflexivity| simpl; lia |].
  iIntros "Hhdr Ha Hp". simpl. g_if_true "Hp".
  iApply ("Hcont" with "Hhdr Ha Hb Hp").
Qed.

(** One iteration of [dequeue_aux]'s loop where the slot is [QNone]
    (or any [ValUnit]-tagged value): drives the iteration to the
    recursive call with [i - 1]. Helper used by [goal_dequeue_at_two]. *)
Lemma goal_dequeue_aux_skip p ks (size range i : Z) (ar back : location)
    (deq : val) dqa atag :
  i ≠ 0%Z →
  (0 ≤ range - i < size)%Z →
  ar ↦ₕ{dqa} Header atag (Z.to_nat size) -∗
  (ar +ₗ (range - i)) ↦ ValUnit -∗
  focused p ks
    (dequeue_aux deq (ValInt size, ValLoc ar, ValLoc back)%V
       (ValInt range) (ValInt i)) -∗
  (ar ↦ₕ{dqa} Header atag (Z.to_nat size) -∗
   (ar +ₗ (range - i)) ↦ ValUnit -∗
   focused p ks
     (dequeue_aux deq (ValInt size, ValLoc ar, ValLoc back)%V
        (ValInt range) (ValInt (i - 1))) -∗ goal ⊤) -∗
  goal ⊤.
Proof.
  iIntros (Hne Hbound) "Hhdr Ha Hp Hcont".
  rewrite {1}/dequeue_aux.
  g_call4 "Hp".
  g_equal "Hp".
  rewrite (bool_decide_eq_false_2 (i = 0)); [|done].
  g_if_false "Hp".
  g_match "Hp".
  g_binop "Hp". g_let "Hp".
  g_get_field_cell "Hp" "Hhdr" "Ha". g_let "Hp".
  g_match "Hp".
  g_binop "Hp".
  iApply ("Hcont" with "Hhdr Ha Hp").
Qed.

(** One iteration of [dequeue_aux]'s loop where the slot holds
    [‘QSome(ValInt w)]: CAS succeeds, the slot is cleared to [QNone],
    and the loop returns [ValInt w]. Helper used by
    [goal_dequeue_at_two] for the final iteration. *)
Lemma goal_dequeue_aux_some p ks (size range i w : Z) (ar back : location)
    (deq : val) dqa atag :
  i ≠ 0%Z →
  (0 ≤ range - i < size)%Z →
  ar ↦ₕ{dqa} Header atag (Z.to_nat size) -∗
  (ar +ₗ (range - i)) ↦ ‘QSome( ValInt w )%V -∗
  focused p ks
    (dequeue_aux deq (ValInt size, ValLoc ar, ValLoc back)%V
       (ValInt range) (ValInt i)) -∗
  (ar ↦ₕ{dqa} Header atag (Z.to_nat size) -∗
   (ar +ₗ (range - i)) ↦ ValUnit -∗
   focused p ks (Val (ValInt w)) -∗ goal ⊤) -∗
  goal ⊤.
Proof.
  iIntros (Hne Hbound) "Hhdr Ha Hp Hcont".
  rewrite {1}/dequeue_aux.
  g_call4 "Hp".
  g_equal "Hp".
  rewrite (bool_decide_eq_false_2 (i = 0)); [|done].
  g_if_false "Hp".
  g_match "Hp".
  g_binop "Hp". g_let "Hp".
  g_get_field_cell "Hp" "Hhdr" "Ha". g_let "Hp".
  g_match "Hp".
  g_block "Hp".
  g_focus (CAS _ _ _) "Hp".
  iApply (focused_cas_succ_cell with "Hp Hhdr Ha"); [reflexivity| simpl; lia |].
  iIntros "Hhdr Ha Hp". simpl. g_if_true "Hp".
  iApply ("Hcont" with "Hhdr Ha Hp").
Qed.

(** Specific helper for the second dequeue in our buggy execution:
    [back = 3], [ar[0] = empty], [ar[1] = empty], [ar[2] = ‘QSome(w)].
    The dequeue scans past the two empty slots and returns [w]. *)
Lemma goal_dequeue_at_two p ks (w : Z) (ar back : location) dqa atag :
  ar ↦ₕ{dqa} Header atag 3 -∗
  back ↦∗ [ValInt 3] -∗
  (ar +ₗ 0) ↦ ValUnit -∗
  (ar +ₗ 1) ↦ ValUnit -∗
  (ar +ₗ 2) ↦ ‘QSome( ValInt w )%V -∗
  focused p ks (dequeue (ValInt 3, ValLoc ar, ValLoc back)%V) -∗
  (ar ↦ₕ{dqa} Header atag 3 -∗
   (ar +ₗ 0) ↦ ValUnit -∗
   (ar +ₗ 1) ↦ ValUnit -∗
   (ar +ₗ 2) ↦ ValUnit -∗
   back ↦∗ [ValInt 3] -∗
   focused p ks (Val (ValInt w)) -∗ goal ⊤) -∗
  goal ⊤.
Proof.
  iIntros "Hhdr Hb Ha0 Ha1 Ha2 Hp Hcont". rewrite /dequeue.
  g_call "Hp".
  g_match "Hp".
  g_get_field "Hp" "Hb".
  g_focus (minimum _ _) "Hp".
  iApply (goal_minimum with "Hp"). iIntros "Hp". simpl.
  rewrite Z.min_l; [|lia]. g_let "Hp".
  (* iter i=3: read ar[0]=QNone, recurse i=2 *)
  iApply (goal_dequeue_aux_skip _ _ 3 3 3 ar back _ _ _ with "Hhdr [Ha0] Hp");
    [done | lia | replace (3 - 3)%Z with 0%Z by lia; iExact "Ha0" |].
  iIntros "Hhdr Ha0 Hp". replace (3 - 1)%Z with 2%Z by lia.
  (* iter i=2: read ar[1]=QNone, recurse i=1 *)
  iApply (goal_dequeue_aux_skip _ _ 3 3 2 ar back _ _ _ with "Hhdr [Ha1] Hp");
    [done | lia | replace (3 - 2)%Z with 1%Z by lia; iExact "Ha1" |].
  iIntros "Hhdr Ha1 Hp". replace (2 - 1)%Z with 1%Z by lia.
  (* iter i=1: read ar[2]=‘QSome(w), CAS success, return w *)
  iApply (goal_dequeue_aux_some _ _ 3 3 1 w ar back _ _ _ with "Hhdr [Ha2] Hp");
    [done | lia | replace (3 - 1)%Z with 2%Z by lia; iExact "Ha2" |].
  iIntros "Hhdr Ha2 Hp".
  replace (ar +ₗ (3 - 3)) with (ar +ₗ 0) by (f_equal; lia).
  replace (ar +ₗ (3 - 2)) with (ar +ₗ 1) by (f_equal; lia).
  replace (ar +ₗ (3 - 1)) with (ar +ₗ 2) by (f_equal; lia).
  iApply ("Hcont" with "Hhdr Ha0 Ha1 Ha2 Hb Hp").
Qed.

Lemma hw_buggy_bug p ks :
  remaining is_stuck' -∗
  focused p ks hw_buggy -∗
  goal ⊤.
Proof.
  iIntros "Hrem Hp". rewrite /hw_buggy.
  (* Setup: allocate the size-3 queue, then [done]. *)
  rewrite /new_queue. g_call "Hp".
  g_focus (Alloc _ _) "Hp".
  iApply (goal_alloc _ _ _ _ 3 with "Hp"); first lia.
  iIntros (ar) "Hhdr Har _ Hp". simpl.
  iDestruct "Har" as "(Ha0 & Ha1 & Ha2 & _)".
  g_let "Hp". g_alloc "Hp" "Htmp".
  iRename select (_ ↦∗ [ValInt 0])%I into "Hb".
  g_let "Hp".
  g_block "Hp". g_let "Hp".
  g_alloc "Hp" "Htmp".
  iRename select (_ ↦∗ [ValBool false])%I into "Hd".
  g_let "Hp".
  (* Fork: forked thread runs [enqueue q 1 ;; done <- true]. *)
  g_fork "Hp" "Hf" "Hfloc". g_let "Hp".
  (* Drive forked through [enqueue]'s prologue + load, parking before the [if]. *)
  g_focus (enqueue _ _) "Hf".
  iApply (goal_enqueue_park with "Hb Hf"). iIntros "Hb Hf". simpl.
  (* Main: full [enqueue 2]. i = 0, ar[0] empty, back = 0. *)
  g_focus (enqueue _ _) "Hp".
  iApply (goal_enqueue_full _ _ 3 0 ar _ _ _ _ with "Hhdr [Ha0] Hb Hp"); first lia.
  { iExact "Ha0". }
  iIntros "Hhdr Ha0 Hb Hp". simpl.
  (* Resume forked: it's now [(if ...) ;; done <- true]. Push the seq
     context into [ks] so [goal_enqueue_resume]'s premise unifies. *)
  iRename select (_ ↦∗ [ValBool false])%I into "Hd'".
  iDestruct (focused_bind_l [CtxLet BAnon _] _ [] with "Hf") as "Hf".
  iApply (goal_enqueue_resume _ _ 3 0 _ _ _ _ _ _ _ with "Hhdr Ha0 Hb Hf"); first lia.
  iIntros "Hhdr Ha0 Hb Hf". simpl.
  (* Forked: [() ;; done <- true] → [done <- true] → [()]. *)
  g_let "Hf". g_set_field "Hf" "Hd'".
  (* Forked is at () now; we drop it (it has finished its body). *)
  g_let "Hp".
  (* Wait loop. [done] is [true] now, so the spin reads true and exits
     on the first iteration. *)
  g_rec "Hp". g_call "Hp".
  g_get_field "Hp" "Hd'". g_if_true "Hp".
  g_let "Hp".
  replace (0 + 1 + 1)%Z with 2%Z by lia.
  (* Main dequeues; returns [1] from [ar[0]] (the survivor of the lost
     update), leaving [ar[0] = QNone], [back = 2]. *)
  g_focus (dequeue _) "Hp".
  iApply (goal_dequeue_at_zero _ _ 3 2 1 ar _ _ with "Hhdr Hb [Ha0] Hp"); [lia|lia| |].
  { iExact "Ha0". }
  iIntros "Hhdr Ha0 Hb Hp". simpl.
  g_let "Hp".
  (* Main enqueues [3] — lands at slot 2 since [back = 2]. *)
  g_focus (enqueue _ _) "Hp".
  iApply (goal_enqueue_full _ _ 3 2 ar _ _ _ _ with "Hhdr [Ha2] Hb Hp"); first lia.
  { iExact "Ha2". }
  iIntros "Hhdr Ha2 Hb Hp". simpl.
  g_let "Hp". replace (2 + 1)%Z with 3%Z by lia.
  (* Second dequeue: scans past the empty [ar[0]] and [ar[1]], returns
     [3] from slot 2. *)
  g_focus (dequeue _) "Hp".
  iApply (goal_dequeue_at_two _ _ _ _ _ _ _ with "Hhdr Hb Ha0 Ha1 Ha2 Hp").
  iIntros "_ _ _ _ _ Hp". simpl.
  (* [let "y" := 3 in assert: "y" < 3] — [3 < 3] is [false]. *)
  g_let "Hp". g_binop "Hp".
  g_assert_stuck "Hp".
Qed.

End bugs.

(** The traced variant of this client lives in [test.hw1_traced]; it
    re-uses the queue ops, [hw_buggy_bug]'s helpers, and adds trace
    bookkeeping via [stdlib.trace]. *)
