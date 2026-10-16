(** lin011_htbl1: lock-free hash table whose try_add reads the bucket and
    then writes it back with a plain atomic store instead of a CAS.

    Witness: two concurrent Add(1, 0) calls (tags 1 and 2). Add(1) reads
    the empty bucket and parks before its store. Add(2) runs to completion,
    returning true. Add(1) resumes, overwrites the bucket from its stale
    snapshot and also returns true. Two completed adds of the same key cannot
    both succeed in any sequential order. Not linearizable. *)

From mizzle.linearizable.support Require Import htbl_prelude.
From mizzle.pure_logic Require Import htbl_model.
From mizzle.linearizable.cases Require Import lin011_htbl1__code lin011_htbl1__types.

Definition init : val := lin011_htbl1٠create.
Definition op : val := lin011_htbl1٠op.

Definition dup_add_trace : list (positive * trace) := [
  (1%positive, Call (‘HAdd( #1, #0 ))%V) ;
  (2%positive, Call (‘HAdd( #1, #0 ))%V) ;
  (2%positive, Ret (ValBool true)) ;
  (1%positive, Ret (ValBool true))
].

Definition gen : val := vfun: <> => ‘Add( #1, #0 ).

Section helpers.
Context `{seqlogGS Σ}.

Lemma goal_gen_add E pp ks :
  running pp (fill ks (gen (Val ValUnit))) -∗
  (running pp (fill ks (Val (‘Add( #1, #0 ))%V)) -∗ goal E) -∗ goal E.
Proof.
  iIntros "Hp Hcont". rewrite /gen. g_call "Hp". g_block "Hp".
Qed.

End helpers.

Lemma dup_add_trace_per_tag_complete : per_tag_complete dup_add_trace.
Proof.
  intros τ.
  destruct (decide (τ = 1%positive)); subst.
  { exists (‘HAdd( #1, #0 ))%V, (ValBool true). right. vm_compute. reflexivity. }
  destruct (decide (τ = 2%positive)); subst.
  { exists (‘HAdd( #1, #0 ))%V, (ValBool true). right. vm_compute. reflexivity. }
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
  rewrite /init /lin011_htbl1٠create. g_call "Hrun".
  g_focus (array٠init _ _)%E "Hrun".
  iApply (goal_array_init_blk _ 0 _ 16 with "Hrun"); first lia.
  iIntros (arr cells Hlen) "#Hhdr Hcells Hrefs Hrun".
  do 17 (destruct cells as [|? cells]; simpl in Hlen; try lia).
  iDestruct "Hcells" as "(_ & Hc1 & _)". iDestruct "Hrefs" as "(_ & Hr1 & _)".
  iSimpl in "Hrun". g_let "Hrun".
  g_rec "Hrun". g_let "Hrun".
  g_rec "Hrun". g_let "Hrun".
  g_call "Hrun".
  iApply (goal_rand _ 0 [CtxIf _ _] false with "Hrun"). iIntros "Hrun". iSimpl in "Hrun". g_if_false "Hrun".
  g_fork "Hrun" "Hk1" "Hl1". g_seq "Hrun". g_binop "Hrun". g_call "Hrun".
  iApply (goal_rand _ 0 [CtxIf _ _] false with "Hrun"). iIntros "Hrun". iSimpl in "Hrun". g_if_false "Hrun".
  g_fork "Hrun" "Hk2" "Hl2". g_seq "Hrun". g_binop "Hrun". g_call "Hrun".
  iApply (goal_rand _ 0 [CtxIf _ _] true with "Hrun"). iIntros "Hrun". iSimpl in "Hrun". g_if_true "Hrun".

  (* tag=1: Add(1,0) -- reads the empty bucket, parks before its store. *)
  iApply (goal_onecall_call ⊤ op #arr gen p' [] 1 (‘Add( #1, #0 ))%V _ goal_gen_add with "Hk1 Htr"). iIntros "Hk1 Htr".
  iEval (rewrite /op /lin011_htbl1٠op) in "Hk1". g_call2 "Hk1". g_match "Hk1".
  rewrite /lin011_htbl1٠try_add. g_call3 "Hk1".
  rewrite /lin011_htbl1٠bucket. g_call2 "Hk1". g_binop "Hk1".
  g_array_get "Hk1" "Hhdr" "Hc1". g_let "Hk1".
  g_get_field "Hk1" "Hr1". g_let "Hk1".
  rewrite /lin011_htbl1٠assoc_mem. g_call2 "Hk1". g_match "Hk1". g_if_false "Hk1". g_block "Hk1".

  (* tag=2: Add(1,0) -- runs to completion, returns true. *)
  iApply (goal_onecall_call ⊤ op #arr gen p'0 [] (1+1) (‘Add( #1, #0 ))%V _ goal_gen_add with "Hk2 Htr"). iIntros "Hk2 Htr".
  iEval (rewrite /op /lin011_htbl1٠op) in "Hk2". g_call2 "Hk2". g_match "Hk2".
  rewrite /lin011_htbl1٠try_add. g_call3 "Hk2".
  rewrite /lin011_htbl1٠bucket. g_call2 "Hk2". g_binop "Hk2".
  g_array_get "Hk2" "Hhdr" "Hc1". g_let "Hk2".
  g_get_field "Hk2" "Hr1". g_let "Hk2".
  rewrite /lin011_htbl1٠assoc_mem. g_call2 "Hk2". g_match "Hk2". g_if_false "Hk2". g_block "Hk2".
  g_set_field "Hk2" "Hr1". g_seq "Hk2".
  iApply (goal_onecall_ret ⊤ p'0 [] (1+1) (ValBool true) _ with "Hk2 Htr"). iIntros "Hk2 Htr".

  (* tag=1: resume -- blind store from the stale snapshot, returns true too. *)
  g_set_field "Hk1" "Hr1". g_seq "Hk1".
  iApply (goal_onecall_ret ⊤ p' [] 1 (ValBool true) _ with "Hk1 Htr"). iIntros "Hk1 Htr".

  iApply (Trace_fulfill with "Hrem Htr").
Qed.
