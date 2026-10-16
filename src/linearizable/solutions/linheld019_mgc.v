(** linheld019_two_lock_queue4: two-lock queue whose pop reads the front cell
    under the head lock, releases the lock, and only later re-acquires it to
    advance the head.

    Two pops can therefore both observe the same front element before either
    advances: both return it, and the two advances move the head twice.

    Witness: Enq(1) (tag 1) completes. Deq (tag 2) and Deq (tag 3) both read
    the front Next(1, _) and release the head lock. Each then advances and
    returns Some 1. A single enqueued 1 dequeued twice: not linearizable. *)

From mizzle.linearizable.support Require Import mgc_prelude.
From mizzle.stdlib Require Import mutex.
From mizzle.pure_logic Require Import queue_opt_model.
From mizzle.linearizable.cases Require Import
  linheld019_two_lock_queue4__code linheld019_two_lock_queue4__types.

Definition init : val := linheld019_two_lock_queue4٠create.
Definition op : val := linheld019_two_lock_queue4٠op.

Definition dup_trace : list (positive * trace) := [
  (1%positive, Call (‘Enq( #1 ))%V) ;
  (1%positive, Ret (§None)%V) ;
  (2%positive, Call (§Deq)%V) ;
  (3%positive, Call (§Deq)%V) ;
  (2%positive, Ret (‘Some( #1 ))%V) ;
  (3%positive, Ret (‘Some( #1 ))%V)
].

Definition gen : val :=
  vfun: <> => if: nondet_bool () then ‘Enq( #1 ) else §Deq.

(* Projection out of an immutable tuple value. *)
Ltac g_proj H := g_pure (GetField _ (Val (ValBlock _ _ _)) (Val _)) H.

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

Lemma goal_gen_deq E pp ks :
  running pp (fill ks (gen (Val ValUnit))) -∗
  (running pp (fill ks (Val (§Deq)%V)) -∗ goal E) -∗ goal E.
Proof.
  iIntros "Hp Hcont". rewrite /gen. g_call "Hp".
  iApply (goal_rand _ pp (CtxIf _ _ :: ks) false with "Hp"). iIntros "Hp".
  iSimpl in "Hp". g_if_false "Hp".
Qed.

End helpers.

Lemma dup_trace_per_tag_complete : per_tag_complete dup_trace.
Proof.
  intros τ.
  destruct (decide (τ = 1%positive)); subst.
  { exists (‘Enq( #1 ))%V, (§None)%V. right. vm_compute. reflexivity. }
  destruct (decide (τ = 2%positive)); subst.
  { exists (§Deq)%V, (‘Some( #1 ))%V. right. vm_compute. reflexivity. }
  destruct (decide (τ = 3%positive)); subst.
  { exists (§Deq)%V, (‘Some( #1 ))%V. right. vm_compute. reflexivity. }
  exists ()%V, ()%V. left.
  unfold dup_trace.
  repeat (rewrite filter_cons_False; [|cbn; intros ?; subst; done]).
  apply filter_nil.
Qed.

Theorem dup_trace_not_linearizable : trace_non_linearizable dup_trace.
Proof.
  apply is_non_linearizable_check_sound.
  - solve_call_valid.
  - exact dup_trace_per_tag_complete.
  - by vm_compute.
Qed.

Theorem mgc_produces_non_linearizable :
  ∃ c κ,
    wf_access.traced_steps ([(most_general_client init op gen)%E], initial_state ValUnit) κ c ∧
    decode_trace κ = dup_trace ∧
    trace_non_linearizable (decode_trace κ).
Proof.
  apply (mgc_non_lin_adequacy (most_general_client init op gen) dup_trace
           dup_trace_not_linearizable).
  intros Σ hG. iIntros "Hrun Htr Hrem".
  rewrite /most_general_client. g_call3 "Hrun".
  rewrite /init /linheld019_two_lock_queue4٠create. g_call "Hrun".
  g_alloc "Hrun" "Hc0". g_let "Hrun".
  g_focus (mutex٠create ())%E "Hrun".
  iApply (focused_mutex_create with "Hrun"). iIntros (lm1) "Hm1 Hrun". iSimpl in "Hrun".
  g_focus (mutex٠create ())%E "Hrun".
  iApply (focused_mutex_create with "Hrun"). iIntros (lm2) "Hm2 Hrun". iSimpl in "Hrun".
  g_alloc "Hrun" "Ht". g_alloc "Hrun" "Hh". g_block "Hrun". g_let "Hrun".
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

  (* tag=1: Enq(1) -- runs to completion. *)
  iApply (goal_onecall_call ⊤ op _ gen p' [] 1 (‘Enq( #1 ))%V _ goal_gen_enq1 with "Hc1 Htr"). iIntros "Hc1 Htr".
  iEval (rewrite /op /linheld019_two_lock_queue4٠op) in "Hc1". g_call2 "Hc1". g_match "Hc1".
  rewrite /linheld019_two_lock_queue4٠push. g_call2 "Hc1".
  g_alloc "Hc1" "Hn". g_let "Hc1".
  g_proj "Hc1". g_focus (mutex٠lock _)%E "Hc1".
  iApply (focused_mutex_lock with "Hm1 Hc1"). iIntros "Hm1 Hc1". iSimpl in "Hc1".
  g_seq "Hc1". g_proj "Hc1". g_get_field "Hc1" "Ht". g_let "Hc1". g_block "Hc1".
  g_set_field "Hc1" "Hc0". g_seq "Hc1".
  g_proj "Hc1". g_set_field "Hc1" "Ht". g_seq "Hc1". g_proj "Hc1".
  g_focus (mutex٠unlock _)%E "Hc1".
  iApply (focused_mutex_unlock with "Hm1 Hc1"). iIntros "Hm1 Hc1". iSimpl in "Hc1".
  g_seq "Hc1".
  iApply (goal_onecall_ret ⊤ p' [] 1 §None%V _ with "Hc1 Htr"). iIntros "Hc1 Htr".
  iSimpl in "Hc0 Ht".

  (* tag=2: Deq -- reads front Next(1, _), releases the head lock. *)
  iApply (goal_onecall_call ⊤ op _ gen p'0 [] (1+1) (§Deq)%V _ goal_gen_deq with "Hc2 Htr"). iIntros "Hc2 Htr".
  iEval (rewrite /op /linheld019_two_lock_queue4٠op) in "Hc2". g_call2 "Hc2". g_match "Hc2".
  rewrite /linheld019_two_lock_queue4٠pop. g_call "Hc2".
  g_proj "Hc2". g_focus (mutex٠lock _)%E "Hc2".
  iApply (focused_mutex_lock with "Hm2 Hc2"). iIntros "Hm2 Hc2". iSimpl in "Hc2".
  g_seq "Hc2". g_proj "Hc2". g_get_field "Hc2" "Hh". g_let "Hc2". g_get_field "Hc2" "Hc0". g_let "Hc2".
  g_proj "Hc2". g_focus (mutex٠unlock _)%E "Hc2".
  iApply (focused_mutex_unlock with "Hm2 Hc2"). iIntros "Hm2 Hc2". iSimpl in "Hc2".
  g_seq "Hc2". g_match "Hc2".

  (* tag=3: Deq -- reads the same front before anyone advanced. *)
  iApply (goal_onecall_call ⊤ op _ gen p'1 [] (1+1+1) (§Deq)%V _ goal_gen_deq with "Hc3 Htr"). iIntros "Hc3 Htr".
  iEval (rewrite /op /linheld019_two_lock_queue4٠op) in "Hc3". g_call2 "Hc3". g_match "Hc3".
  rewrite /linheld019_two_lock_queue4٠pop. g_call "Hc3".
  g_proj "Hc3". g_focus (mutex٠lock _)%E "Hc3".
  iApply (focused_mutex_lock with "Hm2 Hc3"). iIntros "Hm2 Hc3". iSimpl in "Hc3".
  g_seq "Hc3". g_proj "Hc3". g_get_field "Hc3" "Hh". g_let "Hc3". g_get_field "Hc3" "Hc0". g_let "Hc3".
  g_proj "Hc3". g_focus (mutex٠unlock _)%E "Hc3".
  iApply (focused_mutex_unlock with "Hm2 Hc3"). iIntros "Hm2 Hc3". iSimpl in "Hc3".
  g_seq "Hc3". g_match "Hc3".

  (* tag=2: advance (head moves past 1), return Some 1. *)
  rewrite /linheld019_two_lock_queue4٠advance. g_call "Hc2".
  g_proj "Hc2". g_focus (mutex٠lock _)%E "Hc2".
  iApply (focused_mutex_lock with "Hm2 Hc2"). iIntros "Hm2 Hc2". iSimpl in "Hc2".
  g_seq "Hc2". g_proj "Hc2". g_get_field "Hc2" "Hh". g_let "Hc2". g_get_field "Hc2" "Hc0". g_match "Hc2".
  g_proj "Hc2". g_set_field "Hc2" "Hh". g_seq "Hc2". iSimpl in "Hh".
  g_proj "Hc2". g_focus (mutex٠unlock _)%E "Hc2".
  iApply (focused_mutex_unlock with "Hm2 Hc2"). iIntros "Hm2 Hc2". iSimpl in "Hc2".
  g_seq "Hc2". g_block "Hc2".
  iApply (goal_onecall_ret ⊤ p'0 [] (1+1) (‘Some( #1 ))%V _ with "Hc2 Htr"). iIntros "Hc2 Htr".

  (* tag=3: advance finds Nil (no-op), but still returns Some 1. *)
  g_call "Hc3".
  g_proj "Hc3". g_focus (mutex٠lock _)%E "Hc3".
  iApply (focused_mutex_lock with "Hm2 Hc3"). iIntros "Hm2 Hc3". iSimpl in "Hc3".
  g_seq "Hc3". g_proj "Hc3". g_get_field "Hc3" "Hh". g_let "Hc3". g_get_field "Hc3" "Hn". g_match "Hc3".
  g_seq "Hc3".
  g_proj "Hc3". g_focus (mutex٠unlock _)%E "Hc3".
  iApply (focused_mutex_unlock with "Hm2 Hc3"). iIntros "Hm2 Hc3". iSimpl in "Hc3".
  g_seq "Hc3". g_block "Hc3".
  iApply (goal_onecall_ret ⊤ p'1 [] (1+1+1) (‘Some( #1 ))%V _ with "Hc3 Htr"). iIntros "Hc3 Htr".

  iApply (Trace_fulfill with "Hrem Htr").
Qed.
