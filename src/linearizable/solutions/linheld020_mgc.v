(** linheld020_harris_list1: Harris-style sorted list whose remove never
    marks the victim's next pointer: try_remove unlinks a node by a single
    CAS on its predecessor, leaving the removed node's own "next" cell
    writable.

    Witness: Add(1) (tag 1) completes, list = [1]. Add(2) (tag 2) traverses
    to node 1's next cell (Nil), builds its node, and parks before its CAS.
    Remove(1) (tag 3) unlinks node 1 from the head and returns true. Add(2)
    resumes: its CAS on node 1's (now detached) next cell succeeds, so it
    returns true while 2 is unreachable. Mem(2) (tag 4), started after
    Add(2) returned, answers false. No linearization justifies it. *)

From mizzle.linearizable.support Require Import mgc_prelude.
From mizzle.pure_logic Require Import htbl_model.
From mizzle.linearizable.cases Require Import linheld020_harris_list1__code linheld020_harris_list1__types.

Definition init : val := linheld020_harris_list1٠create.
Definition op : val := linheld020_harris_list1٠op.

Definition tr : list (positive * trace) := [
  (1%positive, Call (‘Add( #1, #0 ))%V) ;
  (1%positive, Ret (ValBool true)) ;
  (2%positive, Call (‘Add( #2, #0 ))%V) ;
  (3%positive, Call (‘Remove( #1 ))%V) ;
  (3%positive, Ret (ValBool true)) ;
  (2%positive, Ret (ValBool true)) ;
  (4%positive, Call (‘Mem( #2 ))%V) ;
  (4%positive, Ret (ValBool false))
].

Definition gen : val :=
  vfun: <> =>
    if: nondet_bool () then ‘Add( #1, #0 )
    else if: nondet_bool () then ‘Add( #2, #0 )
    else if: nondet_bool () then ‘Remove( #1 ) else ‘Mem( #2 ).

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

Lemma goal_gen_a2 E pp ks :
  running pp (fill ks (gen (Val ValUnit))) -∗
  (running pp (fill ks (Val (‘Add( #2, #0 ))%V)) -∗ goal E) -∗ goal E.
Proof.
  iIntros "Hp Hcont". rewrite /gen. g_call "Hp".
  iApply (goal_rand _ pp (CtxIf _ _ :: ks) false with "Hp"). iIntros "Hp".
  iSimpl in "Hp". g_if_false "Hp".
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
  iApply (goal_rand _ pp (CtxIf _ _ :: ks) false with "Hp"). iIntros "Hp".
  iSimpl in "Hp". g_if_false "Hp".
  iApply (goal_rand _ pp (CtxIf _ _ :: ks) true with "Hp"). iIntros "Hp".
  iSimpl in "Hp". g_if_true "Hp". g_block "Hp".
Qed.

Lemma goal_gen_m2 E pp ks :
  running pp (fill ks (gen (Val ValUnit))) -∗
  (running pp (fill ks (Val (‘Mem( #2 ))%V)) -∗ goal E) -∗ goal E.
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

Lemma tr_per_tag_complete : per_tag_complete tr.
Proof.
  intros τ.
  destruct (decide (τ = 1%positive)); subst.
  { exists (‘Add( #1, #0 ))%V, (ValBool true). right. vm_compute. reflexivity. }
  destruct (decide (τ = 2%positive)); subst.
  { exists (‘Add( #2, #0 ))%V, (ValBool true). right. vm_compute. reflexivity. }
  destruct (decide (τ = 3%positive)); subst.
  { exists (‘Remove( #1 ))%V, (ValBool true). right. vm_compute. reflexivity. }
  destruct (decide (τ = 4%positive)); subst.
  { exists (‘Mem( #2 ))%V, (ValBool false). right. vm_compute. reflexivity. }
  exists ()%V, ()%V. left.
  unfold tr.
  repeat (rewrite filter_cons_False; [|cbn; intros ?; subst; done]).
  apply filter_nil.
Qed.

Theorem tr_not_linearizable : trace_non_linearizable tr.
Proof.
  apply is_non_linearizable_check_sound.
  - solve_call_valid.
  - exact tr_per_tag_complete.
  - by vm_compute.
Qed.

Theorem mgc_produces_non_linearizable :
  ∃ c κ,
    wf_access.traced_steps ([(most_general_client init op gen)%E], initial_state ValUnit) κ c ∧
    decode_trace κ = tr ∧
    trace_non_linearizable (decode_trace κ).
Proof.
  apply (mgc_non_lin_adequacy (most_general_client init op gen) tr tr_not_linearizable).
  intros Σ hG. iIntros "Hrun Htr Hrem".
  rewrite /most_general_client. g_call3 "Hrun".
  rewrite /init /linheld020_harris_list1٠create. g_call "Hrun".
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

  (* tag=1: Add(1) -- runs to completion, list = [1]. *)
  iApply (goal_onecall_call ⊤ op #l gen p' [] 1 (‘Add( #1, #0 ))%V _ goal_gen_a1 with "Hc1 Htr"). iIntros "Hc1 Htr".
  iEval (rewrite /op /linheld020_harris_list1٠op) in "Hc1". g_call2 "Hc1". g_match "Hc1".
  rewrite /linheld020_harris_list1٠try_add. g_call3 "Hc1".
  rewrite /linheld020_harris_list1٠find. g_call2 "Hc1".
  rewrite /linheld020_harris_list1٠find_from. g_call3 "Hc1".
  g_get_field "Hc1" "Ht". g_let "Hc1". g_match "Hc1".
  g_tuple "Hc1". g_match "Hc1". g_match "Hc1". g_let "Hc1". g_if_false "Hc1".
  g_alloc "Hc1" "Hn1". g_block "Hc1". g_let "Hc1". g_cas_succ "Hc1" "Ht". g_if_true "Hc1".
  iApply (goal_onecall_ret ⊤ p' [] 1 (ValBool true) _ with "Hc1 Htr"). iIntros "Hc1 Htr".

  (* tag=2: Add(2) -- finds prev = node 1's next cell, builds its node,
     parks before the CAS. *)
  iApply (goal_onecall_call ⊤ op #l gen p'0 [] (1+1) (‘Add( #2, #0 ))%V _ goal_gen_a2 with "Hc2 Htr"). iIntros "Hc2 Htr".
  iEval (rewrite /op /linheld020_harris_list1٠op) in "Hc2". g_call2 "Hc2". g_match "Hc2".
  rewrite /linheld020_harris_list1٠try_add. g_call3 "Hc2".
  rewrite /linheld020_harris_list1٠find. g_call2 "Hc2".
  rewrite /linheld020_harris_list1٠find_from. g_call3 "Hc2".
  g_get_field "Hc2" "Ht". g_let "Hc2". g_match "Hc2".
  g_get_field "Hc2" "Hn1". g_match "Hc2". g_binop "Hc2". g_if_true "Hc2".
  g_call3 "Hc2". g_get_field "Hc2" "Hn1". g_let "Hc2". g_match "Hc2".
  g_tuple "Hc2". g_match "Hc2". g_match "Hc2". g_let "Hc2". g_if_false "Hc2".
  g_alloc "Hc2" "Hn2". g_block "Hc2". g_let "Hc2".

  (* tag=3: Remove(1) -- unlinks node 1 from the head without marking it. *)
  iApply (goal_onecall_call ⊤ op #l gen p'1 [] (1+1+1) (‘Remove( #1 ))%V _ goal_gen_r1 with "Hc3 Htr"). iIntros "Hc3 Htr".
  iEval (rewrite /op /linheld020_harris_list1٠op) in "Hc3". g_call2 "Hc3". g_match "Hc3".
  rewrite /linheld020_harris_list1٠try_remove. g_call2 "Hc3".
  rewrite /linheld020_harris_list1٠find. g_call2 "Hc3".
  rewrite /linheld020_harris_list1٠find_from. g_call3 "Hc3".
  g_get_field "Hc3" "Ht". g_let "Hc3". g_match "Hc3".
  g_get_field "Hc3" "Hn1". g_match "Hc3". g_binop "Hc3". g_if_false "Hc3".
  g_tuple "Hc3". g_match "Hc3". g_match "Hc3". g_equal "Hc3". g_if_true "Hc3".
  g_get_field "Hc3" "Hn1". g_match "Hc3". g_cas_succ "Hc3" "Ht". g_if_true "Hc3".
  iApply (goal_onecall_ret ⊤ p'1 [] (1+1+1) (ValBool true) _ with "Hc3 Htr"). iIntros "Hc3 Htr".

  (* tag=2: resume -- CAS on the detached node's next cell succeeds. *)
  g_cas_succ "Hc2" "Hn1". g_if_true "Hc2".
  iApply (goal_onecall_ret ⊤ p'0 [] (1+1) (ValBool true) _ with "Hc2 Htr"). iIntros "Hc2 Htr".

  (* tag=4: Mem(2) -- the list is empty: 2 was lost. *)
  iApply (goal_onecall_call ⊤ op #l gen p'2 [] (1+1+1+1) (‘Mem( #2 ))%V _ goal_gen_m2 with "Hc4 Htr"). iIntros "Hc4 Htr".
  iEval (rewrite /op /linheld020_harris_list1٠op) in "Hc4". g_call2 "Hc4". g_match "Hc4".
  rewrite /linheld020_harris_list1٠mem. g_call2 "Hc4".
  rewrite /linheld020_harris_list1٠find. g_call2 "Hc4".
  rewrite /linheld020_harris_list1٠find_from. g_call3 "Hc4".
  g_get_field "Hc4" "Ht". g_let "Hc4". g_match "Hc4".
  g_tuple "Hc4". g_match "Hc4". g_match "Hc4".
  iApply (goal_onecall_ret ⊤ p'2 [] (1+1+1+1) (ValBool false) _ with "Hc4 Htr"). iIntros "Hc4 Htr".

  iApply (Trace_fulfill with "Hrem Htr").
Qed.
