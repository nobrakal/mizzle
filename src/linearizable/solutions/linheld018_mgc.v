(** linheld018_two_lock_queue3: two-lock queue whose push links the new cell
    into the list only after releasing the tail lock.

    push swings [tail] to its fresh cell under the tail lock, unlocks, and
    only then writes [last <- Next(value, cell)]. A concurrent push may run
    to completion in that window: it links its value after the first push's
    (still unlinked) cell, so the value is unreachable from [head].

    Witness: Enq(1) (tag 1) swaps tail and parks before linking. Enq(2)
    (tag 2) runs to completion. Deq (tag 3) then finds the head cell still
    Nil and returns None, although Enq(2) had completed before it started.
    Enq(1) finally returns. Not linearizable. *)

From mizzle.linearizable.support Require Import mgc_prelude.
From mizzle.stdlib Require Import mutex.
From mizzle.pure_logic Require Import queue_opt_model.
From mizzle.linearizable.cases Require Import
  linheld018_two_lock_queue3__code linheld018_two_lock_queue3__types.

Definition init : val := linheld018_two_lock_queue3٠create.
Definition op : val := linheld018_two_lock_queue3٠op.

Definition unlinked_trace : list (positive * trace) := [
  (1%positive, Call (‘QEnq( #1 ))%V) ;
  (2%positive, Call (‘QEnq( #2 ))%V) ;
  (2%positive, Ret (§None)%V) ;
  (3%positive, Call (§QDeq)%V) ;
  (3%positive, Ret (§None)%V) ;
  (1%positive, Ret (§None)%V)
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

Lemma unlinked_trace_per_tag_complete : per_tag_complete unlinked_trace.
Proof.
  intros τ.
  destruct (decide (τ = 1%positive)); subst.
  { exists (‘QEnq( #1 ))%V, (§None)%V. right. vm_compute. reflexivity. }
  destruct (decide (τ = 2%positive)); subst.
  { exists (‘QEnq( #2 ))%V, (§None)%V. right. vm_compute. reflexivity. }
  destruct (decide (τ = 3%positive)); subst.
  { exists (§QDeq)%V, (§None)%V. right. vm_compute. reflexivity. }
  exists ()%V, ()%V. left.
  unfold unlinked_trace.
  repeat (rewrite filter_cons_False; [|cbn; intros ?; subst; done]).
  apply filter_nil.
Qed.

Theorem unlinked_trace_not_linearizable : trace_non_linearizable unlinked_trace.
Proof.
  apply is_non_linearizable_check_sound.
  - solve_call_valid.
  - exact unlinked_trace_per_tag_complete.
  - by vm_compute.
Qed.

(* A projection out of the (immutable) object tuple is a pure step. *)
Ltac g_proj H := g_pure (GetField _ (Val _) (Val _)) H.

Theorem mgc_produces_non_linearizable :
  ∃ c κ,
    wf_access.traced_steps ([(most_general_client init op gen)%E], initial_state ValUnit) κ c ∧
    decode_trace κ = unlinked_trace ∧
    trace_non_linearizable (decode_trace κ).
Proof.
  apply (mgc_non_lin_adequacy (most_general_client init op gen) unlinked_trace
           unlinked_trace_not_linearizable).
  intros Σ hG. iIntros "Hrun Htr Hrem".
  rewrite /most_general_client. g_call3 "Hrun".
  rewrite /init /linheld018_two_lock_queue3٠create. g_call "Hrun".
  g_alloc "Hrun" "Hc0". g_let "Hrun".
  g_focus (mutex٠create _)%E "Hrun".
  iApply (focused_mutex_create with "Hrun"). iIntros (lt) "Hlt Hrun". iSimpl in "Hrun".
  g_focus (mutex٠create _)%E "Hrun".
  iApply (focused_mutex_create with "Hrun"). iIntros (lh) "Hlh Hrun". iSimpl in "Hrun".
  g_alloc "Hrun" "Ht". g_alloc "Hrun" "Hh". g_block "Hrun". g_let "Hrun".
  g_rec "Hrun". g_let "Hrun".
  g_rec "Hrun". g_let "Hrun".
  g_call "Hrun".
  iApply (goal_rand _ 0 [CtxIf _ _] false with "Hrun"). iIntros "Hrun". iSimpl in "Hrun". g_if_false "Hrun".
  g_fork "Hrun" "Hc1" "Hl1". g_seq "Hrun". g_binop "Hrun". g_call "Hrun".
  iApply (goal_rand _ 0 [CtxIf _ _] false with "Hrun"). iIntros "Hrun". iSimpl in "Hrun". g_if_false "Hrun".
  g_fork "Hrun" "Hc2" "Hl2". g_seq "Hrun". g_binop "Hrun". g_call "Hrun".
  iApply (goal_rand _ 0 [CtxIf _ _] false with "Hrun"). iIntros "Hrun". iSimpl in "Hrun". g_if_false "Hrun".
  g_fork "Hrun" "Hc3" "Hl3". g_seq "Hrun". g_binop "Hrun". g_call "Hrun".
  iApply (goal_rand _ 0 [CtxIf _ _] true with "Hrun"). iIntros "Hrun". iSimpl in "Hrun". g_if_true "Hrun".

  (* tag=1: Enq(1) -- swings tail to its cell, unlocks, parks before linking. *)
  iApply (goal_onecall_call ⊤ op _ gen p' [] 1 (‘Enq( #1 ))%V _ goal_gen_enq1 with "Hc1 Htr"). iIntros "Hc1 Htr".
  iEval (rewrite /op /linheld018_two_lock_queue3٠op) in "Hc1". g_call2 "Hc1". g_match "Hc1".
  rewrite /linheld018_two_lock_queue3٠push. g_call2 "Hc1".
  g_alloc "Hc1" "Hn1". g_let "Hc1".
  g_proj "Hc1". g_focus (mutex٠lock _)%E "Hc1".
  iApply (focused_mutex_lock with "Hlt Hc1"). iIntros "Hlt Hc1". iSimpl in "Hc1".
  g_seq "Hc1". g_proj "Hc1". g_get_field "Hc1" "Ht". g_let "Hc1".
  g_proj "Hc1". g_set_field "Hc1" "Ht". g_seq "Hc1".
  g_proj "Hc1". g_focus (mutex٠unlock _)%E "Hc1".
  iApply (focused_mutex_unlock with "Hlt Hc1"). iIntros "Hlt Hc1". iSimpl in "Hc1".
  g_seq "Hc1". iSimpl in "Ht".

  (* tag=2: Enq(2) -- completes, linking 2 behind Enq(1)'s unlinked cell. *)
  iApply (goal_onecall_call ⊤ op _ gen p'0 [] (1+1) (‘Enq( #2 ))%V _ goal_gen_enq2 with "Hc2 Htr"). iIntros "Hc2 Htr".
  iEval (rewrite /op /linheld018_two_lock_queue3٠op) in "Hc2". g_call2 "Hc2". g_match "Hc2".
  rewrite /linheld018_two_lock_queue3٠push. g_call2 "Hc2".
  g_alloc "Hc2" "Hn2". g_let "Hc2".
  g_proj "Hc2". g_focus (mutex٠lock _)%E "Hc2".
  iApply (focused_mutex_lock with "Hlt Hc2"). iIntros "Hlt Hc2". iSimpl in "Hc2".
  g_seq "Hc2". g_proj "Hc2". g_get_field "Hc2" "Ht". g_let "Hc2".
  g_proj "Hc2". g_set_field "Hc2" "Ht". g_seq "Hc2".
  g_proj "Hc2". g_focus (mutex٠unlock _)%E "Hc2".
  iApply (focused_mutex_unlock with "Hlt Hc2"). iIntros "Hlt Hc2". iSimpl in "Hc2".
  g_seq "Hc2". g_block "Hc2". g_set_field "Hc2" "Hn1". g_seq "Hc2".
  iApply (goal_onecall_ret ⊤ p'0 [] (1+1) §None%V _ with "Hc2 Htr"). iIntros "Hc2 Htr".

  (* tag=3: Deq -- the head cell is still Nil: returns None. *)
  iApply (goal_onecall_call ⊤ op _ gen p'1 [] (1+1+1) (§Deq)%V _ goal_gen_deq with "Hc3 Htr"). iIntros "Hc3 Htr".
  iEval (rewrite /op /linheld018_two_lock_queue3٠op) in "Hc3". g_call2 "Hc3". g_match "Hc3".
  rewrite /linheld018_two_lock_queue3٠pop. g_call "Hc3".
  g_proj "Hc3". g_focus (mutex٠lock _)%E "Hc3".
  iApply (focused_mutex_lock with "Hlh Hc3"). iIntros "Hlh Hc3". iSimpl in "Hc3".
  g_seq "Hc3". g_proj "Hc3". g_get_field "Hc3" "Hh". g_let "Hc3".
  g_get_field "Hc3" "Hc0". g_match "Hc3".
  g_proj "Hc3". g_focus (mutex٠unlock _)%E "Hc3".
  iApply (focused_mutex_unlock with "Hlh Hc3"). iIntros "Hlh Hc3". iSimpl in "Hc3".
  g_seq "Hc3".
  iApply (goal_onecall_ret ⊤ p'1 [] (1+1+1) §None%V _ with "Hc3 Htr"). iIntros "Hc3 Htr".

  (* tag=1: resume -- finally links its cell and returns. *)
  g_block "Hc1". g_set_field "Hc1" "Hc0". g_seq "Hc1".
  iApply (goal_onecall_ret ⊤ p' [] 1 §None%V _ with "Hc1 Htr"). iIntros "Hc1 Htr".

  iApply (Trace_fulfill with "Hrem Htr").
Qed.
