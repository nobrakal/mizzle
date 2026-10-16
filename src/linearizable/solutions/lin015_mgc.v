(** lin015_htbl5: lock-free hash table whose try_add checks membership on
    one snapshot ("old") but CASes against a second, fresh read ("old'").

    Witness: two concurrent Add calls on key 1 (tags 1 and 2). Add(1,1)
    reads the empty bucket and finds key 1 absent, then parks. Add(1,2)
    runs to completion, inserting key 1 and returning true. Add(1,1)
    resumes: its fresh re-read sees the bucket holding key 1, but it does
    not re-check membership; its CAS succeeds and it also returns true.
    In any sequential order the second Add of key 1 must return false.
    Not linearizable. *)

From mizzle.linearizable.support Require Import htbl_prelude.
From mizzle.pure_logic Require Import htbl_model.
From mizzle.linearizable.cases Require Import lin015_htbl5__code lin015_htbl5__types.

Definition init : val := lin015_htbl5٠create.
Definition op : val := lin015_htbl5٠op.

Definition dup_add_trace : list (positive * trace) := [
  (1%positive, Call (‘HAdd( #1, #1 ))%V) ;
  (2%positive, Call (‘HAdd( #1, #2 ))%V) ;
  (2%positive, Ret (ValBool true)) ;
  (1%positive, Ret (ValBool true))
].

Definition gen : val :=
  vfun: <> => if: nondet_bool () then ‘Add( #1, #1 ) else ‘Add( #1, #2 ).

Section helpers.
Context `{seqlogGS Σ}.

Lemma goal_gen_a1 E pp ks :
  running pp (fill ks (gen (Val ValUnit))) -∗
  (running pp (fill ks (Val (‘Add( #1, #1 ))%V)) -∗ goal E) -∗ goal E.
Proof.
  iIntros "Hp Hcont". rewrite /gen. g_call "Hp".
  iApply (goal_rand _ pp (CtxIf _ _ :: ks) true with "Hp"). iIntros "Hp".
  iSimpl in "Hp". g_if_true "Hp". g_block "Hp".
Qed.

Lemma goal_gen_a2 E pp ks :
  running pp (fill ks (gen (Val ValUnit))) -∗
  (running pp (fill ks (Val (‘Add( #1, #2 ))%V)) -∗ goal E) -∗ goal E.
Proof.
  iIntros "Hp Hcont". rewrite /gen. g_call "Hp".
  iApply (goal_rand _ pp (CtxIf _ _ :: ks) false with "Hp"). iIntros "Hp".
  iSimpl in "Hp". g_if_false "Hp". g_block "Hp".
Qed.

End helpers.

Lemma dup_add_trace_per_tag_complete : per_tag_complete dup_add_trace.
Proof.
  intros τ.
  destruct (decide (τ = 1%positive)); subst.
  { exists (‘HAdd( #1, #1 ))%V, (ValBool true). right. vm_compute. reflexivity. }
  destruct (decide (τ = 2%positive)); subst.
  { exists (‘HAdd( #1, #2 ))%V, (ValBool true). right. vm_compute. reflexivity. }
  exists ()%V, ()%V. left.
  unfold dup_add_trace.
  repeat (rewrite filter_cons_False; [|cbn; intros ?; subst; done]).
  apply filter_nil.
Qed.

Theorem dup_add_trace_not_linearizable : trace_non_linearizable dup_add_trace.
Proof.
  apply is_non_linearizable_check_sound.
  - solve_call_valid.
  - exact dup_add_trace_per_tag_complete.
  - by vm_compute.
Qed.

Theorem mgc_produces_non_linearizable :
  ∃ c κ,
    wf_access.traced_steps ([(most_general_client init op gen)%E], initial_state ValUnit) κ c ∧
    decode_trace κ = dup_add_trace ∧
    trace_non_linearizable (decode_trace κ).
Proof.
  apply (mgc_non_lin_adequacy (most_general_client init op gen) dup_add_trace
           dup_add_trace_not_linearizable).
  intros Σ hG. iIntros "Hrun Htr Hrem".
  rewrite /most_general_client. g_call3 "Hrun".
  rewrite /init /lin015_htbl5٠create. g_call "Hrun".
  g_focus (array٠init _ _)%E "Hrun".
  iApply (goal_array_init_blk _ _ _ 16 with "Hrun"); first lia.
  iIntros (arr cells Hlen) "#Hhdr Hcs Hcl Hrun".
  iEval (simpl) in "Hrun". g_let "Hrun".
  g_rec "Hrun". g_let "Hrun".
  g_rec "Hrun". g_let "Hrun".
  g_call "Hrun".
  iApply (goal_rand _ 0 [CtxIf _ _] false with "Hrun"). iIntros "Hrun". iSimpl in "Hrun". g_if_false "Hrun".
  g_fork "Hrun" "Hc1" "Hl1". g_seq "Hrun". g_binop "Hrun". g_call "Hrun".
  iApply (goal_rand _ 0 [CtxIf _ _] false with "Hrun"). iIntros "Hrun". iSimpl in "Hrun". g_if_false "Hrun".
  g_fork "Hrun" "Hc2" "Hl2". g_seq "Hrun". g_binop "Hrun". g_call "Hrun".
  iApply (goal_rand _ 0 [CtxIf _ _] true with "Hrun"). iIntros "Hrun". iSimpl in "Hrun". g_if_true "Hrun".
  do 16 (destruct cells as [|? cells]; first done).
  destruct cells; last done.
  iDestruct "Hcs" as "(? & Hb & _)".
  iDestruct "Hcl" as "(? & Hcl1 & _)".

  (* tag=1: Add(1,1) -- sees bucket 1 empty, parks before the fresh re-read. *)
  iApply (goal_onecall_call ⊤ op #arr gen p' [] 1 (‘Add( #1, #1 ))%V _ goal_gen_a1 with "Hc1 Htr"). iIntros "Hc1 Htr".
  iEval (rewrite /op /lin015_htbl5٠op) in "Hc1". g_call2 "Hc1". g_match "Hc1".
  rewrite /lin015_htbl5٠try_add. g_call3 "Hc1".
  rewrite /lin015_htbl5٠bucket. g_call2 "Hc1". g_args "Hc1".
  g_array_get "Hc1" "Hhdr" "Hb". g_let "Hc1".
  g_get_field "Hc1" "Hcl1". g_let "Hc1".
  rewrite /lin015_htbl5٠assoc_mem. g_call2 "Hc1". g_match "Hc1". g_if_false "Hc1".

  (* tag=2: Add(1,2) -- runs to completion, inserting key 1. *)
  iApply (goal_onecall_call ⊤ op #arr gen p'0 [] (1+1) (‘Add( #1, #2 ))%V _ goal_gen_a2 with "Hc2 Htr"). iIntros "Hc2 Htr".
  iEval (rewrite /op /lin015_htbl5٠op) in "Hc2". g_call2 "Hc2". g_match "Hc2".
  rewrite /lin015_htbl5٠try_add. g_call3 "Hc2".
  rewrite /lin015_htbl5٠bucket. g_call2 "Hc2". g_args "Hc2".
  g_array_get "Hc2" "Hhdr" "Hb". g_let "Hc2".
  g_get_field "Hc2" "Hcl1". g_let "Hc2".
  rewrite /lin015_htbl5٠assoc_mem. g_call2 "Hc2". g_match "Hc2". g_if_false "Hc2".
  g_get_field "Hc2" "Hcl1". g_let "Hc2". g_block "Hc2". g_cas_succ "Hc2" "Hcl1". g_if_true "Hc2".
  iApply (goal_onecall_ret ⊤ p'0 [] (1+1) (ValBool true) _ with "Hc2 Htr"). iIntros "Hc2 Htr".

  (* tag=1: resume -- re-reads without re-checking, CAS succeeds: duplicate. *)
  g_get_field "Hc1" "Hcl1". g_let "Hc1". g_block "Hc1". g_cas_succ "Hc1" "Hcl1". g_if_true "Hc1".
  iApply (goal_onecall_ret ⊤ p' [] 1 (ValBool true) _ with "Hc1 Htr"). iIntros "Hc1 Htr".

  iApply (Trace_fulfill with "Hrem Htr").
Qed.
