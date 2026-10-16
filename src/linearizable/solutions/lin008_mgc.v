(** lin008_ms_queue3: Michael-Scott queue whose pop CASes the head against a
    fresh re-read instead of its snapshot "old_head".

    Witness: Enq(1) (tag 1) completes. Two Deq calls (tags 2 and 3) both read
    the same head cell holding Next(1, next). Deq(3) completes, moving head to
    "next" and returning Some 1. Deq(2) resumes: its fresh re-read sees the
    new head, so its CAS succeeds and it also returns Some 1. One element was
    enqueued but dequeued twice: not linearizable. *)

From mizzle.linearizable.support Require Import mgc_prelude.
From mizzle.pure_logic Require Import queue_opt_model.
From mizzle.linearizable.cases Require Import lin008_ms_queue3__code lin008_ms_queue3__types.

Definition init : val := lin008_ms_queue3٠create.
Definition op : val := lin008_ms_queue3٠op.
Notation valid_op := queue_valid_request.

Definition dup_pop_trace : list (positive * trace) := [
  (1%positive, Call (‘QEnq( #1 ))%V) ;
  (1%positive, Ret (§None)%V) ;
  (2%positive, Call (§QDeq)%V) ;
  (3%positive, Call (§QDeq)%V) ;
  (3%positive, Ret (‘Some( #1 ))%V) ;
  (2%positive, Ret (‘Some( #1 ))%V)
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

Lemma dup_pop_trace_per_tag_complete : per_tag_complete dup_pop_trace.
Proof.
  intros τ.
  destruct (decide (τ = 1%positive)); subst.
  { exists (‘QEnq( #1 ))%V, (§None)%V. right. vm_compute. reflexivity. }
  destruct (decide (τ = 2%positive)); subst.
  { exists (§QDeq)%V, (‘Some( #1 ))%V. right. vm_compute. reflexivity. }
  destruct (decide (τ = 3%positive)); subst.
  { exists (§QDeq)%V, (‘Some( #1 ))%V. right. vm_compute. reflexivity. }
  exists ()%V, ()%V. left.
  unfold dup_pop_trace.
  repeat (rewrite filter_cons_False; [|cbn; intros ?; subst; done]).
  apply filter_nil.
Qed.

Theorem dup_pop_trace_not_linearizable : trace_non_linearizable dup_pop_trace.
Proof.
  apply is_non_linearizable_check_sound.
  - solve_call_valid.
  - exact dup_pop_trace_per_tag_complete.
  - by vm_compute.
Qed.

Theorem mgc_produces_non_linearizable :
  ∃ c κ,
    wf_access.traced_steps ([(most_general_client init op gen)%E], initial_state ValUnit) κ c ∧
    decode_trace κ = dup_pop_trace ∧
    trace_non_linearizable (decode_trace κ).
Proof.
  apply (mgc_non_lin_adequacy (most_general_client init op gen) dup_pop_trace
           dup_pop_trace_not_linearizable).
  intros Σ hG. iIntros "Hrun Htr Hrem".
  rewrite /most_general_client. g_call3 "Hrun".
  rewrite /init /lin008_ms_queue3٠create. g_call "Hrun".
  (* l = sentinel cell, l0 = tail ref, l1 = head ref *)
  g_alloc "Hrun" "Hn0". g_let "Hrun".
  g_alloc "Hrun" "Hb". g_alloc "Hrun" "Ha". g_tuple "Hrun".
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
  iApply (goal_rand _ 0 [CtxIf _ _] true with "Hrun"). iIntros "Hrun". iSimpl in "Hrun". g_if_true "Hrun".

  (* tag=1: Enq(1) -- runs to completion. *)
  iApply (goal_onecall_call ⊤ op (#l1, #l0)%V gen p' [] 1 (‘Enq( #1 ))%V _ goal_gen_enq1 with "Hc1 Htr"). iIntros "Hc1 Htr".
  iEval (rewrite /op /lin008_ms_queue3٠op) in "Hc1". g_call2 "Hc1". g_match "Hc1".
  rewrite /lin008_ms_queue3٠push. g_call2 "Hc1".
  g_alloc "Hc1" "Hnt". g_let "Hc1". g_block "Hc1". g_let "Hc1".
  g_get_field "Hc1" "Hb". g_let "Hc1".
  g_cas_succ "Hc1" "Hn0".
  iSimpl in "Hn0". g_unop "Hc1". g_if_false "Hc1". g_seq "Hc1".
  g_cas_succ "Hc1" "Hb". g_unop "Hc1". g_if_false "Hc1". g_seq "Hc1".
  iApply (goal_onecall_ret ⊤ p' [] 1 §None%V _ with "Hc1 Htr"). iIntros "Hc1 Htr".

  (* tag=2: Deq -- snapshots the head, sees Next(1, _), parks before the CAS. *)
  iApply (goal_onecall_call ⊤ op (#l1, #l0)%V gen p'0 [] (1+1) (§Deq)%V _ goal_gen_deq with "Hc2 Htr"). iIntros "Hc2 Htr".
  iEval (rewrite /op /lin008_ms_queue3٠op) in "Hc2". g_call2 "Hc2". g_match "Hc2".
  rewrite /lin008_ms_queue3٠pop. g_call "Hc2".
  g_get_field "Hc2" "Ha". g_let "Hc2". g_get_field "Hc2" "Hn0". g_match "Hc2".

  (* tag=3: Deq -- runs to completion, returning Some 1. *)
  iApply (goal_onecall_call ⊤ op (#l1, #l0)%V gen p'1 [] (1+1+1) (§Deq)%V _ goal_gen_deq with "Hc3 Htr"). iIntros "Hc3 Htr".
  iEval (rewrite /op /lin008_ms_queue3٠op) in "Hc3". g_call2 "Hc3". g_match "Hc3".
  rewrite /lin008_ms_queue3٠pop. g_call "Hc3".
  g_get_field "Hc3" "Ha". g_let "Hc3". g_get_field "Hc3" "Hn0". g_match "Hc3".
  g_get_field "Hc3" "Ha". g_cas_succ "Hc3" "Ha". g_if_true "Hc3". g_block "Hc3".
  iApply (goal_onecall_ret ⊤ p'1 [] (1+1+1) (‘Some( #1 ))%V _ with "Hc3 Htr"). iIntros "Hc3 Htr".

  (* tag=2: resume -- the fresh re-read sees the new head, the CAS succeeds,
     and 1 is returned a second time. *)
  iSimpl in "Ha".
  g_get_field "Hc2" "Ha". g_cas_succ "Hc2" "Ha". g_if_true "Hc2". g_block "Hc2".
  iApply (goal_onecall_ret ⊤ p'0 [] (1+1) (‘Some( #1 ))%V _ with "Hc2 Htr"). iIntros "Hc2 Htr".
  iApply (Trace_fulfill with "Hrem Htr").
Qed.
