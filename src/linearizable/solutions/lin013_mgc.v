(** lin013_htbl3: hash table whose try_add CASes against a fresh re-read
    instead of its snapshot "old".

    Witness: two concurrent Add(1,1) calls (tags 1 and 2) both read the empty
    bucket 1 and find key 1 absent. Add (tag 2) completes, storing [1] and
    answering true. Add (tag 1) resumes: its fresh re-read sees [1], the CAS
    succeeds, and it also answers true. In any sequential order the second
    Add of key 1 must answer false. Not linearizable. *)

From mizzle.linearizable.support Require Import htbl_prelude.
From mizzle.pure_logic Require Import htbl_model.
From mizzle.linearizable.cases Require Import lin013_htbl3__code lin013_htbl3__types.

Definition init : val := lin013_htbl3٠create.
Definition op : val := lin013_htbl3٠op.

Definition dup_add_trace : list (positive * trace) := [
  (1%positive, Call (‘HAdd( #1, #1 ))%V) ;
  (2%positive, Call (‘HAdd( #1, #1 ))%V) ;
  (2%positive, Ret (ValBool true)) ;
  (1%positive, Ret (ValBool true))
].

Definition gen : val := vfun: <> => ‘Add( #1, #1 ).

Section helpers.
Context `{seqlogGS Σ}.

Lemma goal_gen_add E pp ks :
  running pp (fill ks (gen (Val ValUnit))) -∗
  (running pp (fill ks (Val (‘Add( #1, #1 ))%V)) -∗ goal E) -∗ goal E.
Proof.
  iIntros "Hp Hcont". rewrite /gen. g_call "Hp". g_block "Hp".
Qed.

End helpers.

Lemma dup_add_trace_per_tag_complete : per_tag_complete dup_add_trace.
Proof.
  intros τ.
  destruct (decide (τ = 1%positive)); subst.
  { exists (‘HAdd( #1, #1 ))%V, (ValBool true). right. vm_compute. reflexivity. }
  destruct (decide (τ = 2%positive)); subst.
  { exists (‘HAdd( #1, #1 ))%V, (ValBool true). right. vm_compute. reflexivity. }
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
  rewrite /init /lin013_htbl3٠create. g_call "Hrun".
  g_focus (array٠init _ _)%E "Hrun".
  iApply (goal_array_init_blk _ _ _ 16 with "Hrun"); first lia.
  iIntros (arr cells Hlen) "#Hhdr Hcells Hbk Hrun". iSimpl in "Hrun".
  destruct cells as [|c0 [|c1 rest]]; simpl in Hlen; try lia.
  iDestruct "Hcells" as "[_ [Hc1 _]]". iDestruct "Hbk" as "[_ [Hb1 _]]".
  g_let "Hrun". g_rec "Hrun". g_let "Hrun". g_rec "Hrun". g_let "Hrun". g_call "Hrun".
  iApply (goal_rand _ 0 [CtxIf _ _] false with "Hrun"). iIntros "Hrun". iSimpl in "Hrun". g_if_false "Hrun".
  g_fork "Hrun" "Hc1t" "Hl1". g_seq "Hrun". g_binop "Hrun". g_call "Hrun".
  iApply (goal_rand _ 0 [CtxIf _ _] false with "Hrun"). iIntros "Hrun". iSimpl in "Hrun". g_if_false "Hrun".
  g_fork "Hrun" "Hc2t" "Hl2". g_seq "Hrun". g_binop "Hrun". g_call "Hrun".
  iApply (goal_rand _ 0 [CtxIf _ _] true with "Hrun"). iIntros "Hrun". iSimpl in "Hrun". g_if_true "Hrun".

  (* tag=1: Add(1,1) -- reads the empty bucket, finds 1 absent, parks before
     the CAS's fresh re-read. *)
  iApply (goal_onecall_call ⊤ op #arr gen p' [] 1 (‘Add( #1, #1 ))%V _ goal_gen_add with "Hc1t Htr"). iIntros "Hc1t Htr".
  iEval (rewrite /op /lin013_htbl3٠op) in "Hc1t". g_call2 "Hc1t". g_match "Hc1t".
  rewrite /lin013_htbl3٠try_add. g_call3 "Hc1t".
  rewrite /lin013_htbl3٠bucket. g_call2 "Hc1t". g_args "Hc1t".
  g_array_get "Hc1t" "Hhdr" "Hc1". g_let "Hc1t". g_get_field "Hc1t" "Hb1". g_let "Hc1t".
  rewrite /lin013_htbl3٠assoc_mem. g_call2 "Hc1t". g_match "Hc1t". g_if_false "Hc1t".
  g_block "Hc1t".

  (* tag=2: Add(1,1) -- runs to completion, inserting key 1, answers true. *)
  iApply (goal_onecall_call ⊤ op #arr gen p'0 [] (1+1) (‘Add( #1, #1 ))%V _ goal_gen_add with "Hc2t Htr"). iIntros "Hc2t Htr".
  iEval (rewrite /op /lin013_htbl3٠op) in "Hc2t". g_call2 "Hc2t". g_match "Hc2t".
  rewrite /lin013_htbl3٠try_add. g_call3 "Hc2t".
  rewrite /lin013_htbl3٠bucket. g_call2 "Hc2t". g_args "Hc2t".
  g_array_get "Hc2t" "Hhdr" "Hc1". g_let "Hc2t". g_get_field "Hc2t" "Hb1". g_let "Hc2t".
  rewrite /lin013_htbl3٠assoc_mem. g_call2 "Hc2t". g_match "Hc2t". g_if_false "Hc2t".
  g_block "Hc2t". g_get_field "Hc2t" "Hb1". g_cas_succ "Hc2t" "Hb1". g_if_true "Hc2t".
  iApply (goal_onecall_ret ⊤ p'0 [] (1+1) (ValBool true) _ with "Hc2t Htr"). iIntros "Hc2t Htr".

  (* tag=1: resume -- the fresh re-read sees [1], the CAS succeeds, and the
     duplicate add of key 1 also answers true. *)
  g_get_field "Hc1t" "Hb1". g_cas_succ "Hc1t" "Hb1". g_if_true "Hc1t".
  iApply (goal_onecall_ret ⊤ p' [] 1 (ValBool true) _ with "Hc1t Htr"). iIntros "Hc1t Htr".

  iApply (Trace_fulfill with "Hrem Htr").
Qed.
