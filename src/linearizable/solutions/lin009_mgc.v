(** lin009_ms_queue4: Michael–Scott queue whose push ignores the result of
    the CAS linking the new node after the observed tail.

    If that CAS fails (another push linked first), the new node is never
    linked, yet push still swings (or fixes) the tail to it and returns.

    Witness: Enq(1) reads the tail (the sentinel). Enq(2) runs to
    completion, linking 2 after the sentinel. Enq(1) resumes: its link CAS
    fails (ignored), its tail CAS fails, and fix_tail moves the tail to its
    orphan node. Both enqueues have completed, then two Deqs return
    Some 2 and None: 1 was lost. Not linearizable. *)

From mizzle.linearizable.support Require Import mgc_prelude.
From mizzle.pure_logic Require Import queue_opt_model.
From mizzle.linearizable.cases Require Import lin009_ms_queue4__code lin009_ms_queue4__types.

Definition init : val := lin009_ms_queue4٠create.
Definition op : val := lin009_ms_queue4٠op.

Definition tr : list (positive * trace) := [
  (1%positive, Call (‘Enq( #1 ))%V) ;
  (2%positive, Call (‘Enq( #2 ))%V) ;
  (2%positive, Ret (§None)%V) ;
  (1%positive, Ret (§None)%V) ;
  (3%positive, Call (§Deq)%V) ;
  (3%positive, Ret (‘Some( #2 ))%V) ;
  (4%positive, Call (§Deq)%V) ;
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

Lemma tr_ptc : per_tag_complete tr.
Proof.
  intros τ.
  destruct (decide (τ = 1%positive)); subst.
  { exists (‘Enq( #1 ))%V, (§None)%V. right. vm_compute. reflexivity. }
  destruct (decide (τ = 2%positive)); subst.
  { exists (‘Enq( #2 ))%V, (§None)%V. right. vm_compute. reflexivity. }
  destruct (decide (τ = 3%positive)); subst.
  { exists (§Deq)%V, (‘Some( #2 ))%V. right. vm_compute. reflexivity. }
  destruct (decide (τ = 4%positive)); subst.
  { exists (§Deq)%V, (§None)%V. right. vm_compute. reflexivity. }
  exists ()%V, ()%V. left.
  unfold tr.
  repeat (rewrite filter_cons_False; [|cbn; intros ?; subst; done]).
  apply filter_nil.
Qed.

Theorem tr_nl : trace_non_linearizable tr.
Proof.
  apply is_non_linearizable_check_sound.
  - solve_call_valid.
  - exact tr_ptc.
  - by vm_compute.
Qed.

Theorem mgc_produces_non_linearizable :
  ∃ c κ,
    wf_access.traced_steps ([(most_general_client init op gen)%E], initial_state ValUnit) κ c ∧
    decode_trace κ = tr ∧
    trace_non_linearizable (decode_trace κ).
Proof.
  apply (mgc_non_lin_adequacy (most_general_client init op gen) tr tr_nl).
  intros Σ hG. iIntros "Hrun Htr Hrem".
  rewrite /most_general_client. g_call3 "Hrun".
  rewrite /init /lin009_ms_queue4٠create. g_call "Hrun".
  (* sentinel l; tail ref l0; head ref l1 *)
  g_alloc "Hrun" "Hs". g_let "Hrun".
  g_alloc "Hrun" "Ht". g_alloc "Hrun" "Hh". g_block "Hrun".
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

  (* tag=1: Enq(1) -- reads the tail (the sentinel) and parks. *)
  iApply (goal_onecall_call ⊤ op _ gen p' [] 1 (‘Enq( #1 ))%V _ goal_gen_enq1 with "Hc1 Htr"). iIntros "Hc1 Htr".
  iEval (rewrite /op /lin009_ms_queue4٠op) in "Hc1". g_call2 "Hc1". g_match "Hc1".
  rewrite /lin009_ms_queue4٠push. g_call2 "Hc1".
  g_alloc "Hc1" "Hn1". g_let "Hc1". g_block "Hc1". g_let "Hc1".
  g_get_field "Hc1" "Ht". g_let "Hc1".

  (* tag=2: Enq(2) -- links 2 after the sentinel and swings the tail. *)
  iApply (goal_onecall_call ⊤ op _ gen p'0 [] (1+1) (‘Enq( #2 ))%V _ goal_gen_enq2 with "Hc2 Htr"). iIntros "Hc2 Htr".
  iEval (rewrite /op /lin009_ms_queue4٠op) in "Hc2". g_call2 "Hc2". g_match "Hc2".
  rewrite /lin009_ms_queue4٠push. g_call2 "Hc2".
  g_alloc "Hc2" "Hn2". g_let "Hc2". g_block "Hc2". g_let "Hc2".
  g_get_field "Hc2" "Ht". g_let "Hc2".
  g_cas_succ "Hc2" "Hs". g_seq "Hc2".
  g_cas_succ "Hc2" "Ht". g_unop "Hc2". g_if_false "Hc2". g_seq "Hc2".
  iApply (goal_onecall_ret ⊤ p'0 [] (1+1) §None%V _ with "Hc2 Htr"). iIntros "Hc2 Htr".

  (* tag=1: resume -- the link CAS fails (result ignored), the tail CAS
     fails, and fix_tail moves the tail to the orphan node. *)
  g_cas_fail "Hc1" "Hs". g_seq "Hc1".
  iDestruct (mz_block_cell_acc_Z _ _ _ 0 with "Hn2") as "[Hn2a Hn2r]"; [lia|done|].
  iDestruct (mz_block_cell_acc_Z _ _ _ 0 with "Hs") as "[Hsa Hsr]"; [lia|done|].
  iDestruct (mz_pointsto_ne with "Hn2a Hsa") as %Hne.
  iDestruct ("Hn2r" with "Hn2a") as "Hn2". iDestruct ("Hsr" with "Hsa") as "Hs".
  assert (l3 ≠ l) as Hne' by (intros ->; done).
  g_cas_fail "Hc1" "Ht". g_unop "Hc1". g_if_true "Hc1".
  rewrite /lin009_ms_queue4٠fix_tail. g_call2 "Hc1".
  g_get_field "Hc1" "Ht". g_let "Hc1". g_get_field "Hc1" "Hn1". g_match "Hc1".
  g_cas_succ "Hc1" "Ht". g_unop "Hc1". g_if_false "Hc1". g_seq "Hc1".
  iApply (goal_onecall_ret ⊤ p' [] 1 §None%V _ with "Hc1 Htr"). iIntros "Hc1 Htr".

  (* tag=3: Deq -- returns 2. *)
  iApply (goal_onecall_call ⊤ op _ gen p'1 [] (1+1+1) §Deq%V _ goal_gen_deq with "Hc3 Htr"). iIntros "Hc3 Htr".
  iEval (rewrite /op /lin009_ms_queue4٠op) in "Hc3". g_call2 "Hc3". g_match "Hc3".
  rewrite /lin009_ms_queue4٠pop. g_call "Hc3".
  g_get_field "Hc3" "Hh". g_let "Hc3". g_get_field "Hc3" "Hs". g_match "Hc3".
  g_cas_succ "Hc3" "Hh". g_if_true "Hc3". g_block "Hc3".
  iApply (goal_onecall_ret ⊤ p'1 [] (1+1+1) (‘Some( #2 ))%V _ with "Hc3 Htr"). iIntros "Hc3 Htr".

  (* tag=4: Deq -- empty: 1 was lost although its Enq completed. *)
  iApply (goal_onecall_call ⊤ op _ gen p'2 [] (1+1+1+1) §Deq%V _ goal_gen_deq with "Hc4 Htr"). iIntros "Hc4 Htr".
  iEval (rewrite /op /lin009_ms_queue4٠op) in "Hc4". g_call2 "Hc4". g_match "Hc4".
  rewrite /lin009_ms_queue4٠pop. g_call "Hc4".
  g_get_field "Hc4" "Hh". g_let "Hc4". g_get_field "Hc4" "Hn2". g_match "Hc4".
  iApply (goal_onecall_ret ⊤ p'2 [] (1+1+1+1) §None%V _ with "Hc4 Htr"). iIntros "Hc4 Htr".

  iApply (Trace_fulfill with "Hrem Htr").
Qed.
