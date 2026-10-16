(** key_buggy_stack: Treiber stack whose push compares against a fresh
    re-read instead of its snapshot, under the most general client.

    key_buggy_stack٠push reads the contents into "xs", builds "ys" = v :: xs,
    then CASes with expected value [!ᵃᵗ "t"] -- a second, fresh read -- rather
    than "xs". The CAS therefore always succeeds against whatever is current,
    but stores the list built from the stale "xs": a concurrent push that
    landed in between is silently overwritten, even though it already
    returned.

    Witness: two concurrent Push calls (tags 1 and 2) both read the initial
    (empty) contents. Push(2) (tag 2) completes uncontended, storing [2].
    Push(1) (tag 1) resumes: its fresh re-read sees [2], its CAS succeeds
    against [2], and it stores its stale-based [1], discarding [2] for good.
    Both pushes have completed before two Pop calls (tags 3 and 4) run to
    completion: since Push(2) really completed, every linearization must
    place it somewhere, so the two later Pops must together see two
    elements -- but the real execution yields one (1), then an empty
    response. Not linearizable. *)

From mizzle.linearizable.support Require Import mgc_prelude.

From mizzle.pure_logic Require Import stack_model.
From mizzle.linearizable.cases Require Import
  key_buggy_stack__code key_buggy_stack__types.

Definition init : val := key_buggy_stack٠create.
Definition op : val := key_buggy_stack٠op.

Notation valid_op := stack_valid_request.

Definition lost_push_trace : list (positive * trace) := [
  (1%positive, Call (‘SPush( #1 ))%V) ;
  (2%positive, Call (‘SPush( #2 ))%V) ;
  (2%positive, Ret (§None)%V) ;
  (1%positive, Ret (§None)%V) ;
  (3%positive, Call (§SPop)%V) ;
  (3%positive, Ret (‘Some( #1 ))%V) ;
  (4%positive, Call (§SPop)%V) ;
  (4%positive, Ret (§None)%V)
].

Definition gen : val :=
  vfun: <> =>
    if: nondet_bool () then ‘Push( #1 )
    else if: nondet_bool () then ‘Push( #2 ) else §Pop.

Section helpers.
Context `{seqlogGS Σ}.

Lemma goal_gen_push1 E pp ks :
  running pp (fill ks (gen (Val ValUnit))) -∗
  (running pp (fill ks (Val (‘Push( #1 ))%V)) -∗ goal E) -∗ goal E.
Proof.
  iIntros "Hp Hcont". rewrite /gen. g_call "Hp".
  iApply (goal_rand _ pp (CtxIf _ _ :: ks) true with "Hp"). iIntros "Hp".
  iSimpl in "Hp". g_if_true "Hp". g_block "Hp".
Qed.

Lemma goal_gen_push2 E pp ks :
  running pp (fill ks (gen (Val ValUnit))) -∗
  (running pp (fill ks (Val (‘Push( #2 ))%V)) -∗ goal E) -∗ goal E.
Proof.
  iIntros "Hp Hcont". rewrite /gen. g_call "Hp".
  iApply (goal_rand _ pp (CtxIf _ _ :: ks) false with "Hp"). iIntros "Hp".
  iSimpl in "Hp". g_if_false "Hp".
  iApply (goal_rand _ pp (CtxIf _ _ :: ks) true with "Hp"). iIntros "Hp".
  iSimpl in "Hp". g_if_true "Hp". g_block "Hp".
Qed.

Lemma goal_gen_pop E pp ks :
  running pp (fill ks (gen (Val ValUnit))) -∗
  (running pp (fill ks (Val (§Pop)%V)) -∗ goal E) -∗ goal E.
Proof.
  iIntros "Hp Hcont". rewrite /gen. g_call "Hp".
  iApply (goal_rand _ pp (CtxIf _ _ :: ks) false with "Hp"). iIntros "Hp".
  iSimpl in "Hp". g_if_false "Hp".
  iApply (goal_rand _ pp (CtxIf _ _ :: ks) false with "Hp"). iIntros "Hp".
  iSimpl in "Hp". g_if_false "Hp".
Qed.

End helpers.

Lemma lost_push_trace_per_tag_complete : per_tag_complete lost_push_trace.
Proof.
  intros τ.
  destruct (decide (τ = 1%positive)); subst.
  { exists (‘SPush( #1 ))%V, (§None)%V. right. vm_compute. reflexivity. }
  destruct (decide (τ = 2%positive)); subst.
  { exists (‘SPush( #2 ))%V, (§None)%V. right. vm_compute. reflexivity. }
  destruct (decide (τ = 3%positive)); subst.
  { exists (§SPop)%V, (‘Some( #1 ))%V. right. vm_compute. reflexivity. }
  destruct (decide (τ = 4%positive)); subst.
  { exists (§SPop)%V, (§None)%V. right. vm_compute. reflexivity. }
  exists ()%V, ()%V. left.
  unfold lost_push_trace.
  repeat (rewrite filter_cons_False; [|cbn; intros ?; subst; done]).
  apply filter_nil.
Qed.

Theorem lost_push_trace_not_linearizable : trace_non_linearizable lost_push_trace.
Proof.
  apply is_non_linearizable_check_sound.
  - solve_call_valid.
  - exact lost_push_trace_per_tag_complete.
  - by vm_compute.
Qed.

Theorem mgc_produces_non_linearizable :
  ∃ c κ,
    wf_access.traced_steps ([(most_general_client init op gen)%E], initial_state ValUnit) κ c ∧
    decode_trace κ = lost_push_trace ∧
    trace_non_linearizable (decode_trace κ).
Proof.
  apply (mgc_non_lin_adequacy (most_general_client init op gen) lost_push_trace
           lost_push_trace_not_linearizable).
  intros Σ hG. iIntros "Hrun Htr Hrem".
  rewrite /most_general_client. g_call3 "Hrun".
  rewrite /init /key_buggy_stack٠create. g_call "Hrun".
  g_alloc "Hrun" "Ht". g_let "Hrun".
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

  (* tag=1: Push(1) -- snapshots the empty contents into "xs", builds [1],
     and parks right before the CAS's fresh re-read. *)
  iApply (goal_onecall_call ⊤ op #l gen p' [] 1 (‘Push( #1 ))%V _ goal_gen_push1 with "Hc1 Htr"). iIntros "Hc1 Htr".
  iEval (rewrite /op /key_buggy_stack٠op) in "Hc1". g_call2 "Hc1". g_match "Hc1".
  rewrite /key_buggy_stack٠push. g_call2 "Hc1".
  g_get_field "Hc1" "Ht". g_let "Hc1". g_block "Hc1". g_let "Hc1".

  (* tag=2: Push(2) -- runs to completion uncontended, storing [2]. *)
  iApply (goal_onecall_call ⊤ op #l gen p'0 [] (1+1) (‘Push( #2 ))%V _ goal_gen_push2 with "Hc2 Htr"). iIntros "Hc2 Htr".
  iEval (rewrite /op /key_buggy_stack٠op) in "Hc2". g_call2 "Hc2". g_match "Hc2".
  rewrite /key_buggy_stack٠push. g_call2 "Hc2".
  g_get_field "Hc2" "Ht". g_let "Hc2". g_block "Hc2". g_let "Hc2".
  g_get_field "Hc2" "Ht". g_cas_succ "Hc2" "Ht". g_unop "Hc2". g_if_false "Hc2". g_seq "Hc2".
  iApply (goal_onecall_ret ⊤ p'0 [] (1+1) §None%V _ with "Hc2 Htr"). iIntros "Hc2 Htr".

  (* tag=1: resume -- the fresh re-read sees [2], so the CAS succeeds against
     it and stores the stale-based [1], discarding the completed push of 2. *)
  g_get_field "Hc1" "Ht". g_cas_succ "Hc1" "Ht". g_unop "Hc1". g_if_false "Hc1". g_seq "Hc1".
  iApply (goal_onecall_ret ⊤ p' [] 1 §None%V _ with "Hc1 Htr"). iIntros "Hc1 Htr".

  (* tag=3: Pop -- pops the surviving [1]. *)
  iApply (goal_onecall_call ⊤ op #l gen p'1 [] (1+1+1) §Pop%V _ goal_gen_pop with "Hc3 Htr"). iIntros "Hc3 Htr".
  iEval (rewrite /op /key_buggy_stack٠op) in "Hc3". g_call2 "Hc3". g_match "Hc3".
  rewrite /key_buggy_stack٠pop. g_call "Hc3".
  g_get_field "Hc3" "Ht". g_match "Hc3".
  g_cas_succ "Hc3" "Ht". g_if_true "Hc3". g_block "Hc3".
  iApply (goal_onecall_ret ⊤ p'1 [] (1+1+1) (‘Some( #1 ))%V _ with "Hc3 Htr"). iIntros "Hc3 Htr".

  (* tag=4: Pop -- the stack is empty: [2] was lost, although its push had
     completed before either pop started. *)
  iApply (goal_onecall_call ⊤ op #l gen p'2 [] (1+1+1+1) §Pop%V _ goal_gen_pop with "Hc4 Htr"). iIntros "Hc4 Htr".
  iEval (rewrite /op /key_buggy_stack٠op) in "Hc4". g_call2 "Hc4". g_match "Hc4".
  rewrite /key_buggy_stack٠pop. g_call "Hc4".
  g_get_field "Hc4" "Ht". g_match "Hc4".
  iApply (goal_onecall_ret ⊤ p'2 [] (1+1+1+1) §None%V _ with "Hc4 Htr"). iIntros "Hc4 Htr".

  iApply (Trace_fulfill with "Hrem Htr").
Qed.
