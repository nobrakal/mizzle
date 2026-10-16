(** lin014_htbl4: hash table whose try_add answers [true] even when its CAS
    fails.

    lin014_htbl4٠try_add snapshots the bucket into "old", checks the key is
    absent, then CASes in [Cons(key, value, old)]. On CAS failure it returns
    [true] without retrying, so the key may never have been added.

    Witness: two concurrent Add(1,1) calls (tags 1 and 2) both read the empty
    bucket and see key 1 absent. Add 1 CASes successfully and returns true.
    Add 2's CAS fails against the now non-empty bucket, yet it also returns
    true. Under any sequential order, the second Add of the same key must
    answer false. Not linearizable. *)

From mizzle.linearizable.support Require Import htbl_prelude.
From mizzle.pure_logic Require Import htbl_model.
From mizzle.linearizable.cases Require Import lin014_htbl4__code lin014_htbl4__types.

Definition init : val := lin014_htbl4٠create.
Definition op : val := lin014_htbl4٠op.

Notation valid_op := htbl_valid_request.

Definition double_add_trace : list (positive * trace) := [
  (1%positive, Call (‘HAdd( #1, #1 ))%V) ;
  (2%positive, Call (‘HAdd( #1, #1 ))%V) ;
  (1%positive, Ret (ValBool true)) ;
  (2%positive, Ret (ValBool true))
].

Definition gen : val := vfun: <> => ‘Add( #1, #1 ).

Section helpers.
Context `{seqlogGS Σ}.

Lemma goal_gen_add E pp ks :
  running pp (fill ks (gen (Val ValUnit))) -∗
  (running pp (fill ks (Val (‘Add( #1, #1 ))%V)) -∗ goal E) -∗ goal E.
Proof. iIntros "Hp Hcont". rewrite /gen. g_call "Hp". g_block "Hp". Qed.

End helpers.

Lemma double_add_trace_per_tag_complete : per_tag_complete double_add_trace.
Proof.
  intros τ.
  destruct (decide (τ = 1%positive)); subst.
  { exists (‘HAdd( #1, #1 ))%V, (ValBool true). right. vm_compute. reflexivity. }
  destruct (decide (τ = 2%positive)); subst.
  { exists (‘HAdd( #1, #1 ))%V, (ValBool true). right. vm_compute. reflexivity. }
  exists ()%V, ()%V. left. unfold double_add_trace.
  repeat (rewrite filter_cons_False; [|cbn; intros ?; subst; done]).
  apply filter_nil.
Qed.

Theorem double_add_trace_not_linearizable : trace_non_linearizable double_add_trace.
Proof.
  apply is_non_linearizable_check_sound.
  - solve_call_valid.
  - exact double_add_trace_per_tag_complete.
  - by vm_compute.
Qed.

Theorem mgc_produces_non_linearizable :
  ∃ c κ,
    wf_access.traced_steps ([(most_general_client init op gen)%E], initial_state ValUnit) κ c ∧
    decode_trace κ = double_add_trace ∧
    trace_non_linearizable (decode_trace κ).
Proof.
  apply (mgc_non_lin_adequacy (most_general_client init op gen) double_add_trace
           double_add_trace_not_linearizable).
  intros Σ hG. iIntros "Hrun Htr Hrem".
  rewrite /most_general_client. g_call3 "Hrun".
  rewrite /init /lin014_htbl4٠create. g_call "Hrun".
  g_focus (array٠init _ _)%E "Hrun".
  iApply (goal_array_init_blk _ _ _ 16 with "Hrun"); first lia.
  iIntros (arr cells Hlen) "#Hhdr Hcells Hbs Hrun". iSimpl in "Hrun".
  g_let "Hrun". g_rec "Hrun". g_let "Hrun". g_rec "Hrun". g_let "Hrun". g_call "Hrun".
  iApply (goal_rand _ 0 [CtxIf _ _] false with "Hrun"). iIntros "Hrun". iSimpl in "Hrun". g_if_false "Hrun".
  g_fork "Hrun" "Hc1" "Hl1". g_seq "Hrun". g_binop "Hrun". g_call "Hrun".
  iApply (goal_rand _ 0 [CtxIf _ _] false with "Hrun"). iIntros "Hrun". iSimpl in "Hrun". g_if_false "Hrun".
  g_fork "Hrun" "Hc2" "Hl2". g_seq "Hrun". g_binop "Hrun". g_call "Hrun".
  iApply (goal_rand _ 0 [CtxIf _ _] true with "Hrun"). iIntros "Hrun". iSimpl in "Hrun". g_if_true "Hrun".
  do 2 (destruct cells as [|? cells]; first done).
  iDestruct "Hcells" as "(Hc0 & Hc1' & _)". iDestruct "Hbs" as "(Hb0 & Hb1 & _)".

  (* tag=1: Add(1,1) -- reads the empty bucket 1, finds key 1 absent,
     parks before its CAS. *)
  iApply (goal_onecall_call ⊤ op #arr gen p' [] 1 (‘Add( #1, #1 ))%V _ goal_gen_add with "Hc1 Htr"). iIntros "Hc1 Htr".
  iEval (rewrite /op /lin014_htbl4٠op) in "Hc1". g_call2 "Hc1". g_match "Hc1".
  rewrite /lin014_htbl4٠try_add. g_call3 "Hc1".
  rewrite /lin014_htbl4٠bucket. g_call2 "Hc1". g_args "Hc1".
  replace (Z.land 1 15) with 1%Z by reflexivity.
  g_array_get "Hc1" "Hhdr" "Hc1'". g_let "Hc1". g_get_field "Hc1" "Hb1". g_let "Hc1".
  rewrite /lin014_htbl4٠assoc_mem. g_call2 "Hc1". g_match "Hc1". g_if_false "Hc1".

  (* tag=2: Add(1,1) -- same snapshot, same parking point. *)
  iApply (goal_onecall_call ⊤ op #arr gen p'0 [] (1+1) (‘Add( #1, #1 ))%V _ goal_gen_add with "Hc2 Htr"). iIntros "Hc2 Htr".
  iEval (rewrite /op /lin014_htbl4٠op) in "Hc2". g_call2 "Hc2". g_match "Hc2".
  rewrite /lin014_htbl4٠try_add. g_call3 "Hc2".
  rewrite /lin014_htbl4٠bucket. g_call2 "Hc2". g_args "Hc2".
  replace (Z.land 1 15) with 1%Z by reflexivity.
  g_array_get "Hc2" "Hhdr" "Hc1'". g_let "Hc2". g_get_field "Hc2" "Hb1". g_let "Hc2".
  rewrite /lin014_htbl4٠assoc_mem. g_call2 "Hc2". g_match "Hc2". g_if_false "Hc2".

  (* tag=1: CAS succeeds, returns true. *)
  g_block "Hc1". g_cas_succ "Hc1" "Hb1". g_if_true "Hc1".
  iApply (goal_onecall_ret ⊤ p' [] 1 (ValBool true) _ with "Hc1 Htr"). iIntros "Hc1 Htr".

  (* tag=2: CAS fails, yet still returns true. *)
  g_block "Hc2". g_cas_fail "Hc2" "Hb1". g_if_false "Hc2".
  iApply (goal_onecall_ret ⊤ p'0 [] (1+1) (ValBool true) _ with "Hc2 Htr"). iIntros "Hc2 Htr".

  iApply (Trace_fulfill with "Hrem Htr").
Qed.
