(** linheld022_harris_list3: Harris list whose try_remove ignores the
    result of its marking CAS.

    try_remove finds the node for the key, reads its "next" field into
    "succ", then CASes "next" from "succ" to Marked(succ) -- but discards
    the outcome, unlinks, and returns true regardless. Two concurrent
    removes of the same key can therefore both report success.

    Witness: Add(1,1) (tag 1) completes (true). Remove(1) (tag 2) finds the
    node and reads its unmarked next (Nil), then parks. Remove(1) (tag 3)
    runs to completion: it marks and unlinks the node, returning true.
    Tag 2 resumes: its mark CAS fails (next is now Marked), its unlink CAS
    fails, yet it returns true. Only one Add completed, so at most one of
    the two Removes may answer true. Not linearizable. *)

From mizzle.linearizable.support Require Import mgc_prelude.
From mizzle.pure_logic Require Import htbl_model.
From mizzle.linearizable.cases Require Import linheld022_harris_list3__code linheld022_harris_list3__types.

Definition init : val := linheld022_harris_list3٠create.
Definition op : val := linheld022_harris_list3٠op.

Definition dbl_trace : list (positive * trace) := [
  (1%positive, Call (‘HAdd( #1, #1 ))%V) ;
  (1%positive, Ret (ValBool true)) ;
  (2%positive, Call (‘HRemove( #1 ))%V) ;
  (3%positive, Call (‘HRemove( #1 ))%V) ;
  (3%positive, Ret (ValBool true)) ;
  (2%positive, Ret (ValBool true))
].

Definition gen : val :=
  vfun: <> => if: nondet_bool () then ‘Add( #1, #1 ) else ‘Remove( #1 ).

Section helpers.
Context `{seqlogGS Σ}.

Lemma goal_gen_add E pp ks :
  running pp (fill ks (gen (Val ValUnit))) -∗
  (running pp (fill ks (Val (‘Add( #1, #1 ))%V)) -∗ goal E) -∗ goal E.
Proof.
  iIntros "Hp Hcont". rewrite /gen. g_call "Hp".
  iApply (goal_rand _ pp (CtxIf _ _ :: ks) true with "Hp"). iIntros "Hp".
  iSimpl in "Hp". g_if_true "Hp". g_block "Hp".
Qed.

Lemma goal_gen_rem E pp ks :
  running pp (fill ks (gen (Val ValUnit))) -∗
  (running pp (fill ks (Val (‘Remove( #1 ))%V)) -∗ goal E) -∗ goal E.
Proof.
  iIntros "Hp Hcont". rewrite /gen. g_call "Hp".
  iApply (goal_rand _ pp (CtxIf _ _ :: ks) false with "Hp"). iIntros "Hp".
  iSimpl in "Hp". g_if_false "Hp". g_block "Hp".
Qed.

End helpers.

Lemma dbl_trace_per_tag_complete : per_tag_complete dbl_trace.
Proof.
  intros τ.
  destruct (decide (τ = 1%positive)); subst.
  { exists (‘HAdd( #1, #1 ))%V, (ValBool true). right. vm_compute. reflexivity. }
  destruct (decide (τ = 2%positive)); subst.
  { exists (‘HRemove( #1 ))%V, (ValBool true). right. vm_compute. reflexivity. }
  destruct (decide (τ = 3%positive)); subst.
  { exists (‘HRemove( #1 ))%V, (ValBool true). right. vm_compute. reflexivity. }
  exists ()%V, ()%V. left.
  unfold dbl_trace.
  repeat (rewrite filter_cons_False; [|cbn; intros ?; subst; done]).
  apply filter_nil.
Qed.

Theorem dbl_trace_not_linearizable : trace_non_linearizable dbl_trace.
Proof.
  apply is_non_linearizable_check_sound.
  - solve_call_valid.
  - exact dbl_trace_per_tag_complete.
  - by vm_compute.
Qed.

Theorem mgc_produces_non_linearizable :
  ∃ c κ,
    wf_access.traced_steps ([(most_general_client init op gen)%E], initial_state ValUnit) κ c ∧
    decode_trace κ = dbl_trace ∧
    trace_non_linearizable (decode_trace κ).
Proof.
  apply (mgc_non_lin_adequacy (most_general_client init op gen) dbl_trace
           dbl_trace_not_linearizable).
  intros Σ hG. iIntros "Hrun Htr Hrem".
  rewrite /most_general_client. g_call3 "Hrun".
  rewrite /init /linheld022_harris_list3٠create. g_call "Hrun".
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

  (* tag=1: Add(1,1) -- inserts the node [Cons(1,1,l0)] with l0 ↦ Nil. *)
  iApply (goal_onecall_call ⊤ op #l gen p' [] 1 (‘Add( #1, #1 ))%V _ goal_gen_add with "Hc1 Htr"). iIntros "Hc1 Htr".
  iEval (rewrite /op /linheld022_harris_list3٠op) in "Hc1". g_call2 "Hc1". g_match "Hc1".
  rewrite /linheld022_harris_list3٠try_add. g_call3 "Hc1".
  rewrite /linheld022_harris_list3٠find. g_call2 "Hc1".
  rewrite /linheld022_harris_list3٠find_from. g_call3 "Hc1".
  g_get_field "Hc1" "Ht". g_let "Hc1". g_match "Hc1". g_tuple "Hc1".
  g_match "Hc1". g_match "Hc1". g_let "Hc1". g_if_false "Hc1".
  g_alloc "Hc1" "Hn". g_block "Hc1". g_let "Hc1". g_cas_succ "Hc1" "Ht". g_if_true "Hc1".
  iSimpl in "Ht".
  iApply (goal_onecall_ret ⊤ p' [] 1 (ValBool true) _ with "Hc1 Htr"). iIntros "Hc1 Htr".

  (* tag=2: Remove(1) -- finds the node, reads its unmarked next (Nil),
     and parks before the marking CAS. *)
  iApply (goal_onecall_call ⊤ op #l gen p'0 [] (1+1) (‘Remove( #1 ))%V _ goal_gen_rem with "Hc2 Htr"). iIntros "Hc2 Htr".
  iEval (rewrite /op /linheld022_harris_list3٠op) in "Hc2". g_call2 "Hc2". g_match "Hc2".
  rewrite /linheld022_harris_list3٠try_remove. g_call2 "Hc2".
  rewrite /linheld022_harris_list3٠find. g_call2 "Hc2".
  rewrite /linheld022_harris_list3٠find_from. g_call3 "Hc2".
  g_get_field "Hc2" "Ht". g_let "Hc2". g_match "Hc2". g_get_field "Hc2" "Hn". g_match "Hc2".
  g_binop "Hc2". g_if_false "Hc2". g_tuple "Hc2". g_match "Hc2". g_match "Hc2". g_equal "Hc2". g_if_true "Hc2".
  g_get_field "Hc2" "Hn". g_match "Hc2".

  (* tag=3: Remove(1) -- marks and unlinks the node, returns true. *)
  iApply (goal_onecall_call ⊤ op #l gen p'1 [] (1+1+1) (‘Remove( #1 ))%V _ goal_gen_rem with "Hc3 Htr"). iIntros "Hc3 Htr".
  iEval (rewrite /op /linheld022_harris_list3٠op) in "Hc3". g_call2 "Hc3". g_match "Hc3".
  rewrite /linheld022_harris_list3٠try_remove. g_call2 "Hc3".
  rewrite /linheld022_harris_list3٠find. g_call2 "Hc3".
  rewrite /linheld022_harris_list3٠find_from. g_call3 "Hc3".
  g_get_field "Hc3" "Ht". g_let "Hc3". g_match "Hc3". g_get_field "Hc3" "Hn". g_match "Hc3".
  g_binop "Hc3". g_if_false "Hc3". g_tuple "Hc3". g_match "Hc3". g_match "Hc3". g_equal "Hc3". g_if_true "Hc3".
  g_get_field "Hc3" "Hn". g_match "Hc3".
  g_block "Hc3". g_cas_succ "Hc3" "Hn". g_seq "Hc3". g_cas_succ "Hc3" "Ht". g_seq "Hc3".
  iSimpl in "Hn". iSimpl in "Ht".
  iApply (goal_onecall_ret ⊤ p'1 [] (1+1+1) (ValBool true) _ with "Hc3 Htr"). iIntros "Hc3 Htr".

  (* tag=2: resume -- both CASes fail, but the result is ignored: true. *)
  g_block "Hc2". g_cas_fail "Hc2" "Hn". g_seq "Hc2". g_cas_fail "Hc2" "Ht". g_seq "Hc2".
  iApply (goal_onecall_ret ⊤ p'0 [] (1+1) (ValBool true) _ with "Hc2 Htr"). iIntros "Hc2 Htr".

  iApply (Trace_fulfill with "Hrem Htr").
Qed.
