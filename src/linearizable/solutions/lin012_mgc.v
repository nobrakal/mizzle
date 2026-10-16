(** lin012_htbl2: hash table whose try_remove is a non-atomic
    read-then-store, under the most general client.

    try_remove reads the bucket into "old", then stores
    [remove_list key old] with a plain atomic write instead of a CAS. An add
    to the same bucket that lands between the read and the write is silently
    overwritten, although it already returned.

    Witness: Add(1) completes (bucket 1 = [1]). Remove(1) reads [1] and
    parks before its store. Add(17) (17 land 15 = 1, same bucket) completes,
    storing [17; 1]. Remove(1) resumes and stores [], losing 17. A later
    Mem(17), started after Add(17) returned, answers false. Not
    linearizable. *)

From mizzle.linearizable.support Require Import htbl_prelude.
From mizzle.pure_logic Require Import htbl_model.
From mizzle.linearizable.cases Require Import lin012_htbl2__code lin012_htbl2__types.

Definition init : val := lin012_htbl2٠create.
Definition op : val := lin012_htbl2٠op.

Definition lost_add_trace : list (positive * trace) := [
  (1%positive, Call (‘HAdd( #1, #0 ))%V) ;
  (1%positive, Ret (ValBool true)) ;
  (2%positive, Call (‘HRemove( #1 ))%V) ;
  (3%positive, Call (‘HAdd( #17, #0 ))%V) ;
  (3%positive, Ret (ValBool true)) ;
  (2%positive, Ret (ValBool true)) ;
  (4%positive, Call (‘HMem( #17 ))%V) ;
  (4%positive, Ret (ValBool false))
].

Definition gen : val :=
  vfun: <> =>
    if: nondet_bool () then ‘Add( #1, #0 )
    else if: nondet_bool () then ‘Remove( #1 )
    else if: nondet_bool () then ‘Add( #17, #0 ) else ‘Mem( #17 ).

Section helpers.
Context `{seqlogGS Σ}.

Lemma goal_gen_a1 E pp ks :
  running pp (fill ks (gen (Val ValUnit))) -∗
  (running pp (fill ks (Val (‘Add( #1, #0 ))%V)) -∗ goal E) -∗ goal E.
Proof.
  iIntros "Hp Hcont". rewrite /gen. g_call "Hp".
  iApply (goal_rand _ pp (CtxIf _ _ :: ks) true with "Hp"). iIntros "Hp".
  iSimpl in "Hp". g_if_true "Hp". g_block "Hp".
Qed.

Lemma goal_gen_r1 E pp ks :
  running pp (fill ks (gen (Val ValUnit))) -∗
  (running pp (fill ks (Val (‘Remove( #1 ))%V)) -∗ goal E) -∗ goal E.
Proof.
  iIntros "Hp Hcont". rewrite /gen. g_call "Hp".
  iApply (goal_rand _ pp (CtxIf _ _ :: ks) false with "Hp"). iIntros "Hp".
  iSimpl in "Hp". g_if_false "Hp".
  iApply (goal_rand _ pp (CtxIf _ _ :: ks) true with "Hp"). iIntros "Hp".
  iSimpl in "Hp". g_if_true "Hp". g_block "Hp".
Qed.

Lemma goal_gen_a17 E pp ks :
  running pp (fill ks (gen (Val ValUnit))) -∗
  (running pp (fill ks (Val (‘Add( #17, #0 ))%V)) -∗ goal E) -∗ goal E.
Proof.
  iIntros "Hp Hcont". rewrite /gen. g_call "Hp".
  iApply (goal_rand _ pp (CtxIf _ _ :: ks) false with "Hp"). iIntros "Hp".
  iSimpl in "Hp". g_if_false "Hp".
  iApply (goal_rand _ pp (CtxIf _ _ :: ks) false with "Hp"). iIntros "Hp".
  iSimpl in "Hp". g_if_false "Hp".
  iApply (goal_rand _ pp (CtxIf _ _ :: ks) true with "Hp"). iIntros "Hp".
  iSimpl in "Hp". g_if_true "Hp". g_block "Hp".
Qed.

Lemma goal_gen_m17 E pp ks :
  running pp (fill ks (gen (Val ValUnit))) -∗
  (running pp (fill ks (Val (‘Mem( #17 ))%V)) -∗ goal E) -∗ goal E.
Proof.
  iIntros "Hp Hcont". rewrite /gen. g_call "Hp".
  iApply (goal_rand _ pp (CtxIf _ _ :: ks) false with "Hp"). iIntros "Hp".
  iSimpl in "Hp". g_if_false "Hp".
  iApply (goal_rand _ pp (CtxIf _ _ :: ks) false with "Hp"). iIntros "Hp".
  iSimpl in "Hp". g_if_false "Hp".
  iApply (goal_rand _ pp (CtxIf _ _ :: ks) false with "Hp"). iIntros "Hp".
  iSimpl in "Hp". g_if_false "Hp". g_block "Hp".
Qed.

End helpers.

Lemma lost_add_trace_per_tag_complete : per_tag_complete lost_add_trace.
Proof.
  intros τ.
  destruct (decide (τ = 1%positive)); subst.
  { eexists _, _. right. vm_compute. reflexivity. }
  destruct (decide (τ = 2%positive)); subst.
  { eexists _, _. right. vm_compute. reflexivity. }
  destruct (decide (τ = 3%positive)); subst.
  { eexists _, _. right. vm_compute. reflexivity. }
  destruct (decide (τ = 4%positive)); subst.
  { eexists _, _. right. vm_compute. reflexivity. }
  exists ()%V, ()%V. left. unfold lost_add_trace.
  repeat (rewrite filter_cons_False; [|cbn; intros ?; subst; done]).
  apply filter_nil.
Qed.

Theorem lost_add_trace_not_linearizable : trace_non_linearizable lost_add_trace.
Proof.
  apply is_non_linearizable_check_sound.
  - solve_call_valid.
  - exact lost_add_trace_per_tag_complete.
  - by vm_compute.
Qed.

Theorem mgc_produces_non_linearizable :
  ∃ c κ,
    wf_access.traced_steps ([(most_general_client init op gen)%E], initial_state ValUnit) κ c ∧
    decode_trace κ = lost_add_trace ∧
    trace_non_linearizable (decode_trace κ).
Proof.
  apply (mgc_non_lin_adequacy (most_general_client init op gen) lost_add_trace
           lost_add_trace_not_linearizable).
  intros Σ hG. iIntros "Hrun Htr Hrem".
  rewrite /most_general_client. g_call3 "Hrun".
  rewrite /init /lin012_htbl2٠create. g_call "Hrun".
  g_focus (array٠init _ _)%E "Hrun".
  iApply (goal_array_init_blk _ 0 _ 16 with "Hrun"); first lia.
  iIntros (arr cells Hlen) "#Hhdr Hcells Hc Hrun". iSimpl in "Hrun".
  g_let "Hrun". g_rec "Hrun". g_let "Hrun". g_rec "Hrun". g_let "Hrun". g_call "Hrun".
  iApply (goal_rand _ 0 [CtxIf _ _] false with "Hrun"). iIntros "Hrun". iSimpl in "Hrun". g_if_false "Hrun".
  g_fork "Hrun" "Hc1" "Hl1". g_seq "Hrun". g_binop "Hrun". g_call "Hrun".
  iApply (goal_rand _ 0 [CtxIf _ _] false with "Hrun"). iIntros "Hrun". iSimpl in "Hrun". g_if_false "Hrun".
  g_fork "Hrun" "Hc2" "Hl2". g_seq "Hrun". g_binop "Hrun". g_call "Hrun".
  iApply (goal_rand _ 0 [CtxIf _ _] false with "Hrun"). iIntros "Hrun". iSimpl in "Hrun". g_if_false "Hrun".
  g_fork "Hrun" "Hc3" "Hl3". g_seq "Hrun". g_binop "Hrun". g_call "Hrun".
  iApply (goal_rand _ 0 [CtxIf _ _] false with "Hrun"). iIntros "Hrun". iSimpl in "Hrun". g_if_false "Hrun".
  g_fork "Hrun" "Hc4" "Hl4". g_seq "Hrun". g_binop "Hrun". g_call "Hrun".
  iApply (goal_rand _ 0 [CtxIf _ _] true with "Hrun"). iIntros "Hrun". iSimpl in "Hrun". g_if_true "Hrun".
  (* keep only bucket 1 *)
  do 17 (destruct cells as [|? cells]; simpl in Hlen; try lia).
  iDestruct "Hc" as "(_ & Hb & _)". iDestruct "Hcells" as "(_ & Hb1 & _)".

  (* tag=1: Add(1, 0) -- completes, bucket 1 = [1]. *)
  iApply (goal_onecall_call ⊤ op #arr gen p' [] 1 (‘Add( #1, #0 ))%V _ goal_gen_a1 with "Hc1 Htr"). iIntros "Hc1 Htr".
  iEval (rewrite /op /lin012_htbl2٠op) in "Hc1". g_call2 "Hc1". g_match "Hc1".
  rewrite /lin012_htbl2٠try_add. g_call3 "Hc1".
  rewrite /lin012_htbl2٠bucket. g_call2 "Hc1". g_args "Hc1".
  g_array_get "Hc1" "Hhdr" "Hb1". g_let "Hc1". g_get_field "Hc1" "Hb". g_let "Hc1".
  rewrite /lin012_htbl2٠assoc_mem. g_call2 "Hc1". g_match "Hc1". g_if_false "Hc1".
  g_block "Hc1". g_cas_succ "Hc1" "Hb". g_if_true "Hc1".
  iApply (goal_onecall_ret ⊤ p' [] 1 (ValBool true) _ with "Hc1 Htr"). iIntros "Hc1 Htr".

  (* tag=2: Remove(1) -- reads [1], computes [] and parks before the store. *)
  iApply (goal_onecall_call ⊤ op #arr gen p'0 [] (1+1) (‘Remove( #1 ))%V _ goal_gen_r1 with "Hc2 Htr"). iIntros "Hc2 Htr".
  iEval (rewrite /op /lin012_htbl2٠op) in "Hc2". g_call2 "Hc2". g_match "Hc2".
  rewrite /lin012_htbl2٠try_remove. g_call2 "Hc2".
  rewrite /lin012_htbl2٠bucket. g_call2 "Hc2". g_args "Hc2".
  g_array_get "Hc2" "Hhdr" "Hb1". g_let "Hc2".
  iSimpl in "Hb". g_get_field "Hc2" "Hb". g_let "Hc2".
  rewrite /lin012_htbl2٠assoc_mem. g_call2 "Hc2". g_match "Hc2".
  g_equal "Hc2". g_if_true "Hc2". g_unop "Hc2". g_if_false "Hc2".
  rewrite /lin012_htbl2٠remove_list. g_call2 "Hc2". g_match "Hc2". g_equal "Hc2". g_if_true "Hc2".

  (* tag=3: Add(17, 0) -- same bucket, completes, bucket = [17; 1]. *)
  iApply (goal_onecall_call ⊤ op #arr gen p'1 [] (2+1) (‘Add( #17, #0 ))%V _ goal_gen_a17 with "Hc3 Htr"). iIntros "Hc3 Htr".
  iEval (rewrite /op /lin012_htbl2٠op) in "Hc3". g_call2 "Hc3". g_match "Hc3".
  rewrite /lin012_htbl2٠try_add. g_call3 "Hc3".
  rewrite /lin012_htbl2٠bucket. g_call2 "Hc3". g_args "Hc3".
  g_array_get "Hc3" "Hhdr" "Hb1". g_let "Hc3".
  g_get_field "Hc3" "Hb". g_let "Hc3".
  rewrite /lin012_htbl2٠assoc_mem. g_call2 "Hc3". g_match "Hc3". g_equal "Hc3".
  g_if_false "Hc3". g_call2 "Hc3". g_match "Hc3". g_if_false "Hc3".
  g_block "Hc3". g_cas_succ "Hc3" "Hb". g_if_true "Hc3".
  iApply (goal_onecall_ret ⊤ p'1 [] 3 (ValBool true) _ with "Hc3 Htr"). iIntros "Hc3 Htr".

  (* tag=2: resume -- stores the stale [], erasing 17. *)
  iSimpl in "Hb". g_set_field "Hc2" "Hb". g_seq "Hc2".
  iApply (goal_onecall_ret ⊤ p'0 [] 2 (ValBool true) _ with "Hc2 Htr"). iIntros "Hc2 Htr".

  (* tag=4: Mem(17) -- false, although Add(17) completed. *)
  iApply (goal_onecall_call ⊤ op #arr gen p'2 [] (3+1) (‘Mem( #17 ))%V _ goal_gen_m17 with "Hc4 Htr"). iIntros "Hc4 Htr".
  iEval (rewrite /op /lin012_htbl2٠op) in "Hc4". g_call2 "Hc4". g_match "Hc4".
  rewrite /lin012_htbl2٠mem. g_call2 "Hc4".
  rewrite /lin012_htbl2٠bucket. g_call2 "Hc4". g_args "Hc4".
  g_array_get "Hc4" "Hhdr" "Hb1". g_let "Hc4".
  iSimpl in "Hb". g_get_field "Hc4" "Hb".
  rewrite /lin012_htbl2٠assoc_mem. g_call2 "Hc4". g_match "Hc4".
  iApply (goal_onecall_ret ⊤ p'2 [] 4 (ValBool false) _ with "Hc4 Htr"). iIntros "Hc4 Htr".

  iApply (Trace_fulfill with "Hrem Htr").
Qed.
