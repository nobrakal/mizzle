(** lin007_ms_queue2: Michael–Scott-style queue whose pop advances the head
    with a plain atomic store instead of a CAS.

    Witness: Enq(1) (tag 1) completes. Two Deq calls (tags 2 and 3) both read
    the same head and the same node Next(1, _), then both store the successor
    into head and both return Some 1: one enqueued value is dequeued twice.
    Not linearizable. *)

From mizzle.linearizable.support Require Import mgc_prelude.
From mizzle.pure_logic Require Import queue_opt_model.
From mizzle.linearizable.cases Require Import lin007_ms_queue2__code lin007_ms_queue2__types.

Definition init : val := lin007_ms_queue2٠create.
Definition op : val := lin007_ms_queue2٠op.

Definition dup_trace : list (positive * trace) := [
  (1%positive, Call (‘Enq( #1 ))%V) ;
  (1%positive, Ret (§None)%V) ;
  (2%positive, Call (§Deq)%V) ;
  (3%positive, Call (§Deq)%V) ;
  (2%positive, Ret (‘Some( #1 ))%V) ;
  (3%positive, Ret (‘Some( #1 ))%V)
].

Definition gen : val :=
  vfun: <> => if: nondet_bool () then ‘Enq( #1 ) else §Deq.

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

Lemma goal_gen_deq E pp ks :
  running pp (fill ks (gen (Val ValUnit))) -∗
  (running pp (fill ks (Val (§Deq)%V)) -∗ goal E) -∗ goal E.
Proof.
  iIntros "Hp Hcont". rewrite /gen. g_call "Hp".
  iApply (goal_rand _ pp (CtxIf _ _ :: ks) false with "Hp"). iIntros "Hp".
  iSimpl in "Hp". g_if_false "Hp".
Qed.

End helpers.

Lemma dup_trace_per_tag_complete : per_tag_complete dup_trace.
Proof.
  intros τ.
  destruct (decide (τ = 1%positive)); subst.
  { exists (‘Enq( #1 ))%V, (§None)%V. right. vm_compute. reflexivity. }
  destruct (decide (τ = 2%positive)); subst.
  { exists (§Deq)%V, (‘Some( #1 ))%V. right. vm_compute. reflexivity. }
  destruct (decide (τ = 3%positive)); subst.
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
  rewrite /init /lin007_ms_queue2٠create. g_call "Hrun".
  g_alloc "Hrun" "Hn". g_let "Hrun".
  g_alloc "Hrun" "Htl". g_alloc "Hrun" "Hhd". g_tuple "Hrun". g_let "Hrun".
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

  (* tag=1: Enq(1) -- runs to completion on the empty queue. *)
  iApply (goal_onecall_call ⊤ op (#l1, #l0)%V gen p' [] 1 (‘Enq( #1 ))%V _ goal_gen_enq1 with "Hc1 Htr"). iIntros "Hc1 Htr".
  iEval (rewrite /op /lin007_ms_queue2٠op) in "Hc1". g_call2 "Hc1". g_match "Hc1".
  rewrite /lin007_ms_queue2٠push. g_call2 "Hc1".
  g_alloc "Hc1" "Hnt". g_let "Hc1". g_block "Hc1". g_let "Hc1".
  g_get_field "Hc1" "Htl". g_let "Hc1".
  g_cas_succ "Hc1" "Hn". g_unop "Hc1". g_if_false "Hc1". g_seq "Hc1".
  g_cas_succ "Hc1" "Htl". g_unop "Hc1". g_if_false "Hc1". g_seq "Hc1".
  iApply (goal_onecall_ret ⊤ p' [] 1 §None%V _ with "Hc1 Htr"). iIntros "Hc1 Htr".

  (* tag=2: Deq -- reads head and the node Next(1, _), parks before the store. *)
  iApply (goal_onecall_call ⊤ op (#l1, #l0)%V gen p'0 [] (1+1) (§Deq)%V _ goal_gen_deq with "Hc2 Htr"). iIntros "Hc2 Htr".
  iEval (rewrite /op /lin007_ms_queue2٠op) in "Hc2". g_call2 "Hc2". g_match "Hc2".
  rewrite /lin007_ms_queue2٠pop. g_call "Hc2".
  g_get_field "Hc2" "Hhd". g_let "Hc2". g_get_field "Hc2" "Hn". g_match "Hc2".

  (* tag=3: Deq -- reads the same head and node. *)
  iApply (goal_onecall_call ⊤ op (#l1, #l0)%V gen p'1 [] (1+1+1) (§Deq)%V _ goal_gen_deq with "Hc3 Htr"). iIntros "Hc3 Htr".
  iEval (rewrite /op /lin007_ms_queue2٠op) in "Hc3". g_call2 "Hc3". g_match "Hc3".
  rewrite /lin007_ms_queue2٠pop. g_call "Hc3".
  g_get_field "Hc3" "Hhd". g_let "Hc3". g_get_field "Hc3" "Hn". g_match "Hc3".

  (* Both store the successor unconditionally and both return Some 1. *)
  g_set_field "Hc2" "Hhd". g_seq "Hc2". g_block "Hc2".
  iApply (goal_onecall_ret ⊤ p'0 [] (1+1) (‘Some( #1 ))%V _ with "Hc2 Htr"). iIntros "Hc2 Htr".
  g_set_field "Hc3" "Hhd". g_seq "Hc3". g_block "Hc3".
  iApply (goal_onecall_ret ⊤ p'1 [] (1+1+1) (‘Some( #1 ))%V _ with "Hc3 Htr"). iIntros "Hc3 Htr".
  iApply (Trace_fulfill with "Hrem Htr").
Qed.
