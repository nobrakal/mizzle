From mizzle.test Require Import test_prelude.

From mizzle.stdlib Require Import assert trace.

(** * Queue slot tags *********************************************************
    [QNone] is represented by the same runtime value as [ValUnit].  Since
    freshly allocated arrays are initialized with [ValUnit], a fresh queue
    starts with all slots empty. *)

Notation "'QNone'" :=
  (in_type "test.hw2.qslot" 0)
  (in custom mizzle_tag).
Notation "'QSome'" :=
  (in_type "test.hw2.qslot" 1)
  (in custom mizzle_tag).
Notation "'QAR'" :=
  (in_type "test.hw2.qar" 0)
  (in custom mizzle_tag).

Notation "e1 .{[ e2 ]}" :=
  (GetField NotAtomic e1%E e2%E)
  (at level 2,
   format "e1 .{[ e2 ]}")
  : expr_scope.

(** ** Helper definitions *)

Definition minimum : val := vfun: "m" "n" =>
  if: "m" ≤ "n" then "m" else "n".

Definition diverge : val := vrec: "loop" "v" => "loop" "v".

(** * Buggy queue implementation *********************************************

    This file demonstrates a different bug from [hw1].

    In [hw1], the interesting race is between two enqueues: both can reserve
    the same slot because the slot write and [back] increment are not atomic.

    Here, the interesting race is between two dequeues.  The dequeue operation
    scans for a non-empty slot, but when it finds one it clears the slot with a
    plain [SetField] instead of claiming it with [CAS].  Two dequeuers can both
    read the same [QSome v] before either store occurs, and then both return
    [v].  That duplicates one logical queue element, which is impossible for a
    linearizable queue. *)

Definition new_queue : val :=
  vfun: "sz" =>
    let: "ar"   := Alloc (Val (ValNat (in_type "test.hw2.qar" 0))) "sz" in
    let: "back" := ref 0 in
    ("sz", "ar", "back").

Definition enqueue : val :=
  vfun: "q" "x" =>
    let: "q_size", "q_ar", "q_back" := "q" in
    let: "i" := "q_back".{[#0]} in
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
          SetField NotAtomic "q_ar" "j" (§QNone) ;;
          "v"
      end
    ).

Definition dequeue : val :=
  vrec: "dequeue" "q" =>
    let: "q_size", "q_ar", "q_back" := "q" in
    let: "range" := minimum "q_back".{[#0]} "q_size" in
    dequeue_aux "dequeue" "q" "range" "range".

(** * Buggy test program *****************************************************

    The client enqueues a single value [7], then forks a dequeuer while the
    main thread also dequeues.  With a linearizable queue, at most one of those
    dequeues can return [7].  The other dequeue would have to return a later
    value or keep waiting.

    The buggy execution is:

    - forked dequeue reads [ar[0] = QSome 7] and parks before clearing it;
    - main dequeue reads the same [ar[0] = QSome 7];
    - main clears [ar[0]] and returns [7];
    - forked dequeue resumes, clears [ar[0]] again, and also returns [7];
    - the final assertion becomes [7 < 7], so it gets stuck.

    The assertion uses an ordering predicate rather than inequality because it
    gives a concrete stuck endpoint when both returned values are equal. *)

Definition hw2_buggy : expr :=
  let: "q" := new_queue 1 in
  let: "r" := ref 0 in
  let: "done" := ref false in
  enqueue "q" 7 ;;
  Fork (
    let: "x" := dequeue "q" in
    "r" <- "x" ;;
    "done" <- true
  ) ;;
  let: "y" := dequeue "q" in
  (rec: "wait" <> => if: !"done" then () else ("wait" ())) () ;;
  assert: "y" < !"r".

Section bugs.
Context `{seqlogGS Σ}.

(** ** Helper specs **********************************************************
    These are the proof steps needed to drive the bad interleaving.  They are
    intentionally written against the public [enqueue]/[dequeue] values and
    unfold the definitions locally. *)

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
  iDestruct (focused_bind_l [CtxLet (BNamed "i") _] with "Hp") as "Hp".
  g_get_field "Hp" "Hb". g_let "Hp".
  iApply ("Hcont" with "Hb Hp").
Qed.

Lemma goal_enqueue_resume p ks (size i b : Z) (ar back : location) (x vl : val) :
  (0 ≤ i)%Z →
  (i < size)%Z →
  ar ↦ₕ□ Header (in_type "test.hw2.qar" 0) (Z.to_nat size) -∗
  (ar +ₗ i) ↦ vl -∗
  back ↦∗ [ValInt b] -∗
  focused p ks
    (if: (ValInt i) < (ValInt size) then (
       SetField NotAtomic (ValLoc ar) (ValInt i) (‘QSome( x )) ;;
       FAA (ValLoc back).[contents] 1 ;; ()
     ) else (
       diverge ()
     )) -∗
  ((ar +ₗ i) ↦ ‘QSome( x )%V -∗
   back ↦∗ [ValInt (b + 1)] -∗
   focused p ks (Val ValUnit) -∗ goal ⊤) -∗
  goal ⊤.
Proof.
  iIntros (Hlo Hbound) "Hhdr Hi Hb Hp Hcont".
  g_binop "Hp".
  rewrite (bool_decide_eq_true_2 _ Hbound).
  g_if_true "Hp".
  g_block "Hp".
  iDestruct (focused_bind_l [CtxLet BAnon _] with "Hp") as "Hp".
  iDestruct (focused_bind_l [CtxSetField3 NotAtomic #ar #i] with "Hp") as "Hp".
  iEval (simpl) in "Hp".
  iDestruct (focused_bind_l [CtxLet BAnon _] with "Hp") as "Hp".
  iApply (focused_set_field_cell_at ⊤ [] with "Hp Hhdr Hi").
  { simpl. rewrite Z2Nat.id; lia. }
  iIntros "Hhdr Hi Hp". simpl.
  g_let "Hp".
  g_block "Hp".
  g_focus (FAA _ _) "Hp".
  iApply (focused_faa with "Hp Hb").
  { vm_compute. done. }
  { vm_compute. reflexivity. }
  iIntros "Hb Hp". simpl.
  g_let "Hp".
  iApply ("Hcont" with "Hi Hb Hp").
Qed.

Lemma goal_enqueue_full p ks (size i : Z) (ar back : location) (x : val) :
  (0 ≤ i)%Z →
  (i < size)%Z →
  ar ↦ₕ□ Header (in_type "test.hw2.qar" 0) (Z.to_nat size) -∗
  (ar +ₗ i) ↦ ValUnit -∗
  back ↦∗ [ValInt i] -∗
  focused p ks (enqueue (ValInt size, ValLoc ar, ValLoc back)%V x) -∗
  ((ar +ₗ i) ↦ ‘QSome( x )%V -∗
   back ↦∗ [ValInt (i + 1)] -∗
   focused p ks (Val ValUnit) -∗ goal ⊤) -∗
  goal ⊤.
Proof.
  iIntros (Hlo Hbound) "Hhdr Hi Hb Hp Hcont".
  iApply (goal_enqueue_park with "Hb Hp"). iIntros "Hb Hp". simpl.
  iApply (goal_enqueue_resume with "Hhdr Hi Hb Hp"); [done|done|].
  iIntros "Hi Hb Hp".
  iApply ("Hcont" with "Hi Hb Hp").
Qed.

(** Drive [dequeue] to the point immediately after it has loaded a non-empty
    slot but before it has executed the plain store that clears the slot. *)
Lemma goal_dequeue_park_after_load
    p ks (size range i w : Z) (ar back : location) :
  i ≠ 0%Z →
  (0 ≤ range - i < size)%Z →
  ar ↦ₕ□ Header (in_type "test.hw2.qar" 0) (Z.to_nat size) -∗
  back ↦∗ [ValInt range] -∗
  (ar +ₗ (range - i)) ↦ ‘QSome( ValInt w )%V -∗
  focused p ks (dequeue_aux dequeue (ValInt size, ValLoc ar, ValLoc back)%V
                   (ValInt range) (ValInt i)) -∗
  (ar ↦ₕ□ Header (in_type "test.hw2.qar" 0) (Z.to_nat size) -∗
   back ↦∗ [ValInt range] -∗
   (ar +ₗ (range - i)) ↦ ‘QSome( ValInt w )%V -∗
   focused p ks
     (SetField NotAtomic (ValLoc ar) (ValInt (range - i)) (§QNone) ;;
      Val (ValInt w)) -∗
   goal ⊤) -∗
  goal ⊤.
Proof.
  iIntros (Hne Hidx) "Hhdr Hb Ha Hp Hcont".
  rewrite {1}/dequeue_aux.
  g_call4 "Hp".
  g_equal "Hp".
  rewrite (bool_decide_eq_false_2 (i = 0)); [|done].
  g_if_false "Hp".
  g_match "Hp".
  g_binop "Hp". g_let "Hp".
  iDestruct (focused_bind_l [CtxLet (BNamed "x") _] with "Hp") as "Hp".
  g_get_field_cell "Hp" "Hhdr" "Ha". g_let "Hp".
  g_match "Hp".
  iApply ("Hcont" with "Hhdr Hb Ha Hp").
Qed.

Lemma goal_dequeue_finish_after_load
    p ks (size range i w : Z) (ar : location) (vl : val) :
  (0 ≤ range - i < size)%Z →
  ar ↦ₕ□ Header (in_type "test.hw2.qar" 0) (Z.to_nat size) -∗
  (ar +ₗ (range - i)) ↦ vl -∗
  focused p ks
    (SetField NotAtomic (ValLoc ar) (ValInt (range - i)) (§QNone) ;;
     Val (ValInt w)) -∗
  ((ar +ₗ (range - i)) ↦ ValUnit -∗
   focused p ks (Val (ValInt w)) -∗ goal ⊤) -∗
  goal ⊤.
Proof.
  iIntros (Hidx) "Hhdr Ha Hp Hcont".
  iDestruct (focused_bind_l [CtxLet BAnon _] with "Hp") as "Hp".
  g_set_field_cell "Hp" "Hhdr" "Ha". g_let "Hp".
  iApply ("Hcont" with "Ha Hp").
Qed.

(** A full successful sequential dequeue from slot zero.  This is only used to
    set up simple examples; the bad interleaving instead parks two dequeuers
    (see the note at the end of the file). *)
Lemma goal_dequeue_at_zero p ks (size b w : Z) (ar back : location) :
  (1 ≤ b)%Z →
  (b ≤ size)%Z →
  ar ↦ₕ□ Header (in_type "test.hw2.qar" 0) (Z.to_nat size) -∗
  back ↦∗ [ValInt b] -∗
  (ar +ₗ 0) ↦ ‘QSome( ValInt w )%V -∗
  focused p ks (dequeue (ValInt size, ValLoc ar, ValLoc back)%V) -∗
  ((ar +ₗ 0) ↦ ValUnit -∗
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
  iApply (goal_dequeue_park_after_load _ _ size b b w ar back
            with "Hhdr Hb [Ha] Hp").
  - lia.
  - lia.
  - replace (b - b)%Z with 0%Z by lia. iExact "Ha".
  - iIntros "Hhdr Hb Ha Hp".
    iApply (goal_dequeue_finish_after_load _ _ size b b w ar
              with "Hhdr [Ha] Hp").
    { lia. }
    { replace (b - b)%Z with 0%Z by lia. iExact "Ha". }
    iIntros "Ha Hp".
    replace (ar +ₗ (b - b)) with (ar +ₗ 0) by (f_equal; lia).
    iApply ("Hcont" with "Ha Hb Hp").
Qed.

End bugs.

(** No end-to-end proof of [hw2_buggy] is given: the bad interleaving is
    only prepared by the helper lemmas above.  The critical proof move is to apply
    [goal_dequeue_park_after_load] to two focused threads before applying
    [goal_dequeue_finish_after_load] to either one; since the implementation
    uses [SetField] rather than [CAS], both parked threads have already committed
    to returning the same loaded value. *)
