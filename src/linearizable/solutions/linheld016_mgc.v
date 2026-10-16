(** linheld016_two_lock_queue1: two-lock queue whose push never takes the
    tail lock.

    push reads "last" := t.tail, writes Next(v, cell) into "last", then
    advances t.tail -- all without holding tail_lock. Two concurrent pushes
    can both read the same tail cell; the second write of Next(...) into it
    overwrites the first, unlinking the first pushed element for good.

    Witness: Enq(1) (tag 1) and Enq(2) (tag 2) both read the initial tail
    cell. Enq(1) completes, linking 1; Enq(2) completes, overwriting the link
    with 2. Both enqueues have returned before two Deq calls (tags 3 and 4):
    every linearization must hold both 1 and 2, but the real execution
    dequeues 2, then reports empty. Not linearizable. *)

From mizzle.linearizable.support Require Import mgc_prelude.
From mizzle.stdlib Require Import mutex.
From mizzle.linearizable.cases Require Import linheld016_two_lock_queue1__code linheld016_two_lock_queue1__types.
From mizzle.pure_logic Require Import queue_opt_model.

Definition init : val := linheld016_two_lock_queue1٠create.
Definition op : val := linheld016_two_lock_queue1٠op.

Definition lost_enq_trace : list (positive * trace) := [
  (1%positive, Call (‘QEnq( #1 ))%V) ;
  (2%positive, Call (‘QEnq( #2 ))%V) ;
  (1%positive, Ret (§None)%V) ;
  (2%positive, Ret (§None)%V) ;
  (3%positive, Call (§QDeq)%V) ;
  (3%positive, Ret (‘Some( #2 ))%V) ;
  (4%positive, Call (§QDeq)%V) ;
  (4%positive, Ret (§None)%V)
].

Definition gen : val :=
  vfun: <> =>
    if: nondet_bool () then ‘Enq( #1 )
    else if: nondet_bool () then ‘Enq( #2 ) else §Deq.

Section helpers.
Context `{seqlogGS Σ}.

Lemma goal_gen_enq1 E pp ks :
  running pp (fill ks (gen (Val ValUnit))) -∗
  (running pp (fill ks (Val (‘Enq( #1 ))%V)) -∗ goal E) -∗ goal E.
Proof.
  iIntros "Hp Hcont". rewrite /gen. g_call "Hp".
  iApply (goal_rand _ pp (CtxIf _ _ :: ks) true with "Hp"). iIntros "Hp".
  iSimpl in "Hp". g_if_true "Hp". g_block "Hp".
Qed.

Lemma goal_gen_enq2 E pp ks :
  running pp (fill ks (gen (Val ValUnit))) -∗
  (running pp (fill ks (Val (‘Enq( #2 ))%V)) -∗ goal E) -∗ goal E.
Proof.
  iIntros "Hp Hcont". rewrite /gen. g_call "Hp".
  iApply (goal_rand _ pp (CtxIf _ _ :: ks) false with "Hp"). iIntros "Hp".
  iSimpl in "Hp". g_if_false "Hp".
  iApply (goal_rand _ pp (CtxIf _ _ :: ks) true with "Hp"). iIntros "Hp".
  iSimpl in "Hp". g_if_true "Hp". g_block "Hp".
Qed.

Lemma goal_gen_deq E pp ks :
  running pp (fill ks (gen (Val ValUnit))) -∗
  (running pp (fill ks (Val (§Deq)%V)) -∗ goal E) -∗ goal E.
Proof.
  iIntros "Hp Hcont". rewrite /gen. g_call "Hp".
  iApply (goal_rand _ pp (CtxIf _ _ :: ks) false with "Hp"). iIntros "Hp".
  iSimpl in "Hp". g_if_false "Hp".
  iApply (goal_rand _ pp (CtxIf _ _ :: ks) false with "Hp"). iIntros "Hp".
  iSimpl in "Hp". g_if_false "Hp".
Qed.

End helpers.

Lemma lost_enq_trace_per_tag_complete : per_tag_complete lost_enq_trace.
Proof.
  intros τ.
  destruct (decide (τ = 1%positive)); subst.
  { exists (‘QEnq( #1 ))%V, (§None)%V. right. vm_compute. reflexivity. }
  destruct (decide (τ = 2%positive)); subst.
  { exists (‘QEnq( #2 ))%V, (§None)%V. right. vm_compute. reflexivity. }
  destruct (decide (τ = 3%positive)); subst.
  { exists (§QDeq)%V, (‘Some( #2 ))%V. right. vm_compute. reflexivity. }
  destruct (decide (τ = 4%positive)); subst.
  { exists (§QDeq)%V, (§None)%V. right. vm_compute. reflexivity. }
  exists ()%V, ()%V. left.
  unfold lost_enq_trace.
  repeat (rewrite filter_cons_False; [|cbn; intros ?; subst; done]).
  apply filter_nil.
Qed.

Theorem lost_enq_trace_not_linearizable : trace_non_linearizable lost_enq_trace.
Proof.
  apply is_non_linearizable_check_sound.
  - solve_call_valid.
  - exact lost_enq_trace_per_tag_complete.
  - by vm_compute.
Qed.

Theorem mgc_produces_non_linearizable :
  ∃ c κ,
    wf_access.traced_steps ([(most_general_client init op gen)%E], initial_state ValUnit) κ c ∧
    decode_trace κ = lost_enq_trace ∧
    trace_non_linearizable (decode_trace κ).
Proof.
  apply (mgc_non_lin_adequacy (most_general_client init op gen) lost_enq_trace
           lost_enq_trace_not_linearizable).
  intros Σ hG. iIntros "Hrun Htr Hrem".
  rewrite /most_general_client. g_call3 "Hrun".
  rewrite /init /linheld016_two_lock_queue1٠create. g_call "Hrun".
  g_alloc "Hrun" "Hc0". g_let "Hrun".
  g_focus (mutex٠create _)%E "Hrun".
  iApply (focused_mutex_create with "Hrun"). iIntros (m1) "Hm1 Hrun". iSimpl in "Hrun".
  g_focus (mutex٠create _)%E "Hrun".
  iApply (focused_mutex_create with "Hrun"). iIntros (m2) "Hm2 Hrun". iSimpl in "Hrun".
  g_alloc "Hrun" "Htl". g_alloc "Hrun" "Hhd". g_block "Hrun".
  g_let "Hrun".
  g_rec "Hrun". g_let "Hrun".
  g_rec "Hrun". g_let "Hrun".
  g_call "Hrun".
  iApply (goal_rand _ 0 [CtxIf _ _] false with "Hrun"). iIntros "Hrun". iSimpl in "Hrun". g_if_false "Hrun".
  g_fork "Hrun" "Hc1" "Hl1". g_seq "Hrun". g_binop "Hrun". g_call "Hrun".
  iApply (goal_rand _ 0 [CtxIf _ _] false with "Hrun"). iIntros "Hrun". iSimpl in "Hrun". g_if_false "Hrun".
  g_fork "Hrun" "Hc2" "Hl2". g_seq "Hrun". g_binop "Hrun". g_call "Hrun".
  iApply (goal_rand _ 0 [CtxIf _ _] false with "Hrun"). iIntros "Hrun". iSimpl in "Hrun". g_if_false "Hrun".
  g_fork "Hrun" "Hc3" "Hl3". g_seq "Hrun". g_binop "Hrun". g_call "Hrun".
  iApply (goal_rand _ 0 [CtxIf _ _] false with "Hrun"). iIntros "Hrun". iSimpl in "Hrun". g_if_false "Hrun".
  g_fork "Hrun" "Hc4" "Hl4". g_seq "Hrun". g_binop "Hrun". g_call "Hrun".
  iApply (goal_rand _ 0 [CtxIf _ _] true with "Hrun"). iIntros "Hrun". iSimpl in "Hrun". g_if_true "Hrun".

  (* tag=1: Enq(1) -- reads the initial tail cell, parks. *)
  iApply (goal_onecall_call ⊤ op _ gen p' [] 1 (‘QEnq( #1 ))%V _ goal_gen_enq1 with "Hc1 Htr"). iIntros "Hc1 Htr".
  iEval (rewrite /op /linheld016_two_lock_queue1٠op) in "Hc1". g_call2 "Hc1". g_match "Hc1".
  rewrite /linheld016_two_lock_queue1٠push. g_call2 "Hc1".
  g_alloc "Hc1" "Hn1". g_let "Hc1".
  g_get_field "Hc1" "Htl". g_let "Hc1".

  (* tag=2: Enq(2) -- reads the same tail cell, parks. *)
  iApply (goal_onecall_call ⊤ op _ gen p'0 [] (1+1) (‘QEnq( #2 ))%V _ goal_gen_enq2 with "Hc2 Htr"). iIntros "Hc2 Htr".
  iEval (rewrite /op /linheld016_two_lock_queue1٠op) in "Hc2". g_call2 "Hc2". g_match "Hc2".
  rewrite /linheld016_two_lock_queue1٠push. g_call2 "Hc2".
  g_alloc "Hc2" "Hn2". g_let "Hc2".
  g_get_field "Hc2" "Htl". g_let "Hc2".

  (* tag=1 completes: links Next(1, _) into the shared cell. *)
  g_block "Hc1". g_set_field "Hc1" "Hc0". g_seq "Hc1". g_set_field "Hc1" "Htl". g_seq "Hc1".
  iApply (goal_onecall_ret ⊤ p' [] 1 §None%V _ with "Hc1 Htr"). iIntros "Hc1 Htr".

  (* tag=2 completes: overwrites the link with Next(2, _), losing 1. *)
  g_block "Hc2". g_set_field "Hc2" "Hc0". g_seq "Hc2". g_set_field "Hc2" "Htl". g_seq "Hc2".
  iApply (goal_onecall_ret ⊤ p'0 [] (1+1) §None%V _ with "Hc2 Htr"). iIntros "Hc2 Htr".

  (* tag=3: Deq -- returns 2. *)
  iApply (goal_onecall_call ⊤ op _ gen p'1 [] (1+1+1) §QDeq%V _ goal_gen_deq with "Hc3 Htr"). iIntros "Hc3 Htr".
  iEval (rewrite /op /linheld016_two_lock_queue1٠op) in "Hc3". g_call2 "Hc3". g_match "Hc3".
  rewrite /linheld016_two_lock_queue1٠pop. g_call "Hc3".
  g_pure (GetField _ _ _) "Hc3".
  g_focus (mutex٠lock _)%E "Hc3". iApply (focused_mutex_lock with "Hm2 Hc3"). iIntros "Hm2 Hc3". iSimpl in "Hc3".
  g_seq "Hc3". g_get_field "Hc3" "Hhd". g_let "Hc3". g_get_field "Hc3" "Hc0". g_match "Hc3".
  g_set_field "Hc3" "Hhd". g_seq "Hc3". g_pure (GetField _ _ _) "Hc3".
  g_focus (mutex٠unlock _)%E "Hc3". iApply (focused_mutex_unlock with "Hm2 Hc3"). iIntros "Hm2 Hc3". iSimpl in "Hc3".
  g_seq "Hc3". g_block "Hc3".
  iApply (goal_onecall_ret ⊤ p'1 [] (1+1+1) (‘Some( #2 ))%V _ with "Hc3 Htr"). iIntros "Hc3 Htr".

  (* tag=4: Deq -- the queue is empty: 1 was lost. *)
  iApply (goal_onecall_call ⊤ op _ gen p'2 [] (1+1+1+1) §QDeq%V _ goal_gen_deq with "Hc4 Htr"). iIntros "Hc4 Htr".
  iEval (rewrite /op /linheld016_two_lock_queue1٠op) in "Hc4". g_call2 "Hc4". g_match "Hc4".
  rewrite /linheld016_two_lock_queue1٠pop. g_call "Hc4".
  g_pure (GetField _ _ _) "Hc4".
  g_focus (mutex٠lock _)%E "Hc4". iApply (focused_mutex_lock with "Hm2 Hc4"). iIntros "Hm2 Hc4". iSimpl in "Hc4".
  g_seq "Hc4". g_get_field "Hc4" "Hhd". g_let "Hc4". g_get_field "Hc4" "Hn2". g_match "Hc4".
  g_pure (GetField _ _ _) "Hc4".
  g_focus (mutex٠unlock _)%E "Hc4". iApply (focused_mutex_unlock with "Hm2 Hc4"). iIntros "Hm2 Hc4". iSimpl in "Hc4".
  g_seq "Hc4".
  iApply (goal_onecall_ret ⊤ p'2 [] (1+1+1+1) §None%V _ with "Hc4 Htr"). iIntros "Hc4 Htr".

  iApply (Trace_fulfill with "Hrem Htr").
Qed.
