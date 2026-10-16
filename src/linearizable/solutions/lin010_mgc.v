(** lin010_ms_queue5: Michael-Scott queue whose pop returns the value read
    by a preliminary peek, but CASes the head read afterwards.

    pop first calls peek_opt (reads head, then the first node's value), then
    re-reads head into "old_head" and CASes it to its successor. If another
    pop completes in between, "old_head" is a later node: the CAS succeeds
    and removes that node, but the stale peeked value is returned.

    Witness: Enq(1), Enq(2) complete. Deq (tag 3) peeks 1 and parks. Deq
    (tag 4) runs to completion, returning 1. Deq 3 resumes, removes node 2
    and returns 1 again. 1 was dequeued twice and 2 is lost. Not
    linearizable. *)

From mizzle.linearizable.support Require Import mgc_prelude.
From mizzle.pure_logic Require Import queue_opt_model.
From mizzle.linearizable.cases Require Import lin010_ms_queue5__code lin010_ms_queue5__types.

Definition init : val := lin010_ms_queue5٠create.
Definition op : val := lin010_ms_queue5٠op.

Definition dup_trace : list (positive * trace) := [
  (1%positive, Call (‘Enq( #1 ))%V) ;
  (1%positive, Ret (§None)%V) ;
  (2%positive, Call (‘Enq( #2 ))%V) ;
  (2%positive, Ret (§None)%V) ;
  (3%positive, Call (§Deq)%V) ;
  (4%positive, Call (§Deq)%V) ;
  (4%positive, Ret (‘Some( #1 ))%V) ;
  (3%positive, Ret (‘Some( #1 ))%V)
].

Definition gen : val :=
  vfun: <> =>
    if: nondet_bool () then ‘Enq( #1 )
    else if: nondet_bool () then ‘Enq( #2 ) else §Deq.

Lemma dup_trace_per_tag_complete : per_tag_complete dup_trace.
Proof.
  intros τ.
  destruct (decide (τ = 1%positive)); subst.
  { exists (‘Enq( #1 ))%V, (§None)%V. right. vm_compute. reflexivity. }
  destruct (decide (τ = 2%positive)); subst.
  { exists (‘Enq( #2 ))%V, (§None)%V. right. vm_compute. reflexivity. }
  destruct (decide (τ = 3%positive)); subst.
  { exists (§Deq)%V, (‘Some( #1 ))%V. right. vm_compute. reflexivity. }
  destruct (decide (τ = 4%positive)); subst.
  { exists (§Deq)%V, (‘Some( #1 ))%V. right. vm_compute. reflexivity. }
  exists ()%V, ()%V. left.
  unfold dup_trace.
  repeat (rewrite filter_cons_False; [|cbn; intros ?; subst; done]).
  apply filter_nil.
Qed.

Theorem dup_trace_not_linearizable : trace_non_linearizable dup_trace.
Proof.
  apply is_non_linearizable_check_sound.
  - solve_call_valid.
  - exact dup_trace_per_tag_complete.
  - by vm_compute.
Qed.

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

Theorem mgc_produces_non_linearizable :
  ∃ c κ,
    wf_access.traced_steps ([(most_general_client init op gen)%E], initial_state ValUnit) κ c ∧
    decode_trace κ = dup_trace ∧
    trace_non_linearizable (decode_trace κ).
Proof.
  apply (mgc_non_lin_adequacy (most_general_client init op gen) dup_trace
           dup_trace_not_linearizable).
  intros Σ hG. iIntros "Hrun Htr Hrem".
  rewrite /most_general_client. g_call3 "Hrun".
  rewrite /init /lin010_ms_queue5٠create. g_call "Hrun".
  g_alloc "Hrun" "Hn". g_let "Hrun".
  g_alloc "Hrun" "Htl". g_alloc "Hrun" "Hhd". g_tuple "Hrun".
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

  (* tag=1: Enq(1) -- links node 1 after the sentinel, swings the tail. *)
  iApply (goal_onecall_call ⊤ op _ gen p' [] 1 (‘Enq( #1 ))%V _ goal_gen_enq1 with "Hc1 Htr"). iIntros "Hc1 Htr".
  iEval (rewrite /op /lin010_ms_queue5٠op) in "Hc1". g_call2 "Hc1". g_match "Hc1".
  rewrite /lin010_ms_queue5٠push. g_call2 "Hc1".
  g_alloc "Hc1" "Hn1". g_let "Hc1". g_block "Hc1". g_let "Hc1".
  g_get_field "Hc1" "Htl". g_let "Hc1".
  g_cas_succ "Hc1" "Hn". g_unop "Hc1". g_if_false "Hc1". g_seq "Hc1".
  g_cas_succ "Hc1" "Htl". g_unop "Hc1". g_if_false "Hc1". g_seq "Hc1".
  iApply (goal_onecall_ret ⊤ p' [] 1 §None%V _ with "Hc1 Htr"). iIntros "Hc1 Htr".
  iSimpl in "Hn Htl".

  (* tag=2: Enq(2) -- same, after node 1. *)
  iApply (goal_onecall_call ⊤ op _ gen p'0 [] (1+1) (‘Enq( #2 ))%V _ goal_gen_enq2 with "Hc2 Htr"). iIntros "Hc2 Htr".
  iEval (rewrite /op /lin010_ms_queue5٠op) in "Hc2". g_call2 "Hc2". g_match "Hc2".
  rewrite /lin010_ms_queue5٠push. g_call2 "Hc2".
  g_alloc "Hc2" "Hn2". g_let "Hc2". g_block "Hc2". g_let "Hc2".
  g_get_field "Hc2" "Htl". g_let "Hc2".
  g_cas_succ "Hc2" "Hn1". g_unop "Hc2". g_if_false "Hc2". g_seq "Hc2".
  g_cas_succ "Hc2" "Htl". g_unop "Hc2". g_if_false "Hc2". g_seq "Hc2".
  iApply (goal_onecall_ret ⊤ p'0 [] (1+1) §None%V _ with "Hc2 Htr"). iIntros "Hc2 Htr".
  iSimpl in "Hn1 Htl".

  (* tag=3: Deq -- peeks value 1, parks before re-reading the head. *)
  iApply (goal_onecall_call ⊤ op _ gen p'1 [] (1+1+1) §Deq%V _ goal_gen_deq with "Hc3 Htr"). iIntros "Hc3 Htr".
  iEval (rewrite /op /lin010_ms_queue5٠op) in "Hc3". g_call2 "Hc3". g_match "Hc3".
  rewrite /lin010_ms_queue5٠pop. g_call "Hc3".
  rewrite /lin010_ms_queue5٠peek_opt. g_call "Hc3".
  g_get_field "Hc3" "Hhd". g_let "Hc3". g_get_field "Hc3" "Hn". g_match "Hc3". g_block "Hc3". g_match "Hc3".

  (* tag=4: Deq -- runs to completion, dequeuing 1. *)
  iApply (goal_onecall_call ⊤ op _ gen p'2 [] (1+1+1+1) §Deq%V _ goal_gen_deq with "Hc4 Htr"). iIntros "Hc4 Htr".
  iEval (rewrite /op /lin010_ms_queue5٠op) in "Hc4". g_call2 "Hc4". g_match "Hc4".
  rewrite /lin010_ms_queue5٠pop. g_call "Hc4".
  rewrite /lin010_ms_queue5٠peek_opt. g_call "Hc4".
  g_get_field "Hc4" "Hhd". g_let "Hc4". g_get_field "Hc4" "Hn". g_match "Hc4". g_block "Hc4". g_match "Hc4".
  g_get_field "Hc4" "Hhd". g_let "Hc4". g_get_field "Hc4" "Hn". g_match "Hc4".
  g_cas_succ "Hc4" "Hhd". g_if_true "Hc4". g_block "Hc4".
  iApply (goal_onecall_ret ⊤ p'2 [] (1+1+1+1) (‘Some( #1 ))%V _ with "Hc4 Htr"). iIntros "Hc4 Htr".
  iSimpl in "Hhd".

  (* tag=3: resume -- removes node 2 but returns the stale peeked 1. *)
  g_get_field "Hc3" "Hhd". g_let "Hc3". g_get_field "Hc3" "Hn1". g_match "Hc3".
  g_cas_succ "Hc3" "Hhd". g_if_true "Hc3". g_block "Hc3".
  iApply (goal_onecall_ret ⊤ p'1 [] (1+1+1) (‘Some( #1 ))%V _ with "Hc3 Htr"). iIntros "Hc3 Htr".

  iApply (Trace_fulfill with "Hrem Htr").
Qed.
