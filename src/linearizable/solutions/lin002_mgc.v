(** lin002_treiber_stack2: Treiber stack whose pop is not atomic, under the
    most general client.

    lin002_treiber_stack2٠pop reads the contents, then unconditionally
    overwrites them with the tail via a plain atomic store instead of a CAS.
    Two concurrent pops can both read the same head and both return it.

    Witness: Push(1) (tag 1) completes. Pops (tags 2 and 3) both read [1],
    then both store [] and both return Some 1. One element was pushed but
    two pops returned it. Not linearizable. *)

From mizzle.linearizable.support Require Import mgc_prelude.
From mizzle.pure_logic Require Import stack_model.
From mizzle.linearizable.cases Require Import lin002_treiber_stack2__code lin002_treiber_stack2__types.

Definition init : val := lin002_treiber_stack2٠create.
Definition op : val := lin002_treiber_stack2٠op.

Notation valid_op := stack_valid_request.

Definition double_pop_trace : list (positive * trace) := [
  (1%positive, Call (‘SPush( #1 ))%V) ;
  (1%positive, Ret (§None)%V) ;
  (2%positive, Call (§SPop)%V) ;
  (3%positive, Call (§SPop)%V) ;
  (2%positive, Ret (‘Some( #1 ))%V) ;
  (3%positive, Ret (‘Some( #1 ))%V)
].

Definition gen : val :=
  vfun: <> => if: nondet_bool () then ‘Push( #1 ) else §Pop.

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

Lemma goal_gen_pop E pp ks :
  running pp (fill ks (gen (Val ValUnit))) -∗
  (running pp (fill ks (Val (§Pop)%V)) -∗ goal E) -∗ goal E.
Proof.
  iIntros "Hp Hcont". rewrite /gen. g_call "Hp".
  iApply (goal_rand _ pp (CtxIf _ _ :: ks) false with "Hp"). iIntros "Hp".
  iSimpl in "Hp". g_if_false "Hp".
Qed.

End helpers.

Lemma double_pop_trace_per_tag_complete : per_tag_complete double_pop_trace.
Proof.
  intros τ.
  destruct (decide (τ = 1%positive)); subst.
  { exists (‘SPush( #1 ))%V, (§None)%V. right. vm_compute. reflexivity. }
  destruct (decide (τ = 2%positive)); subst.
  { exists (§SPop)%V, (‘Some( #1 ))%V. right. vm_compute. reflexivity. }
  destruct (decide (τ = 3%positive)); subst.
  { exists (§SPop)%V, (‘Some( #1 ))%V. right. vm_compute. reflexivity. }
  exists ()%V, ()%V. left.
  unfold double_pop_trace.
  repeat (rewrite filter_cons_False; [|cbn; intros ?; subst; done]).
  apply filter_nil.
Qed.

Theorem double_pop_trace_not_linearizable : trace_non_linearizable double_pop_trace.
Proof.
  apply is_non_linearizable_check_sound.
  - solve_call_valid.
  - exact double_pop_trace_per_tag_complete.
  - by vm_compute.
Qed.

Theorem mgc_produces_non_linearizable :
  ∃ c κ,
    wf_access.traced_steps ([(most_general_client init op gen)%E], initial_state ValUnit) κ c ∧
    decode_trace κ = double_pop_trace ∧
    trace_non_linearizable (decode_trace κ).
Proof.
  apply (mgc_non_lin_adequacy (most_general_client init op gen) double_pop_trace
           double_pop_trace_not_linearizable).
  intros Σ hG. iIntros "Hrun Htr Hrem".
  rewrite /most_general_client. g_call3 "Hrun".
  rewrite /init /lin002_treiber_stack2٠create. g_call "Hrun".
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
  iApply (goal_rand _ 0 [CtxIf _ _] true with "Hrun"). iIntros "Hrun". iSimpl in "Hrun". g_if_true "Hrun".

  (* tag=1: Push(1) -- completes uncontended, storing [1]. *)
  iApply (goal_onecall_call ⊤ op #l gen p' [] 1 (‘Push( #1 ))%V _ goal_gen_push1 with "Hc1 Htr"). iIntros "Hc1 Htr".
  iEval (rewrite /op /lin002_treiber_stack2٠op) in "Hc1". g_call2 "Hc1". g_match "Hc1".
  rewrite /lin002_treiber_stack2٠push. g_call2 "Hc1".
  g_get_field "Hc1" "Ht". g_let "Hc1". g_block "Hc1". g_let "Hc1".
  g_cas_succ "Hc1" "Ht". g_unop "Hc1". g_if_false "Hc1". g_seq "Hc1".
  iApply (goal_onecall_ret ⊤ p' [] 1 §None%V _ with "Hc1 Htr"). iIntros "Hc1 Htr".

  (* tag=2: Pop -- reads [1] and parks before its store. *)
  iApply (goal_onecall_call ⊤ op #l gen p'0 [] (1+1) §Pop%V _ goal_gen_pop with "Hc2 Htr"). iIntros "Hc2 Htr".
  iEval (rewrite /op /lin002_treiber_stack2٠op) in "Hc2". g_call2 "Hc2". g_match "Hc2".
  rewrite /lin002_treiber_stack2٠pop. g_call "Hc2".
  g_get_field "Hc2" "Ht". g_match "Hc2".

  (* tag=3: Pop -- also reads [1]. *)
  iApply (goal_onecall_call ⊤ op #l gen p'1 [] (1+1+1) §Pop%V _ goal_gen_pop with "Hc3 Htr"). iIntros "Hc3 Htr".
  iEval (rewrite /op /lin002_treiber_stack2٠op) in "Hc3". g_call2 "Hc3". g_match "Hc3".
  rewrite /lin002_treiber_stack2٠pop. g_call "Hc3".
  g_get_field "Hc3" "Ht". g_match "Hc3".

  (* Both pops store [] and both return Some 1. *)
  g_set_field "Hc2" "Ht". g_seq "Hc2". g_block "Hc2".
  iApply (goal_onecall_ret ⊤ p'0 [] (1+1) (‘Some( #1 ))%V _ with "Hc2 Htr"). iIntros "Hc2 Htr".
  g_set_field "Hc3" "Ht". g_seq "Hc3". g_block "Hc3".
  iApply (goal_onecall_ret ⊤ p'1 [] (1+1+1) (‘Some( #1 ))%V _ with "Hc3 Htr"). iIntros "Hc3 Htr".

  iApply (Trace_fulfill with "Hrem Htr").
Qed.
