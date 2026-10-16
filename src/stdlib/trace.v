From iris.proofmode Require Import base proofmode.

From mizzle.lang Require Import instances.
From mizzle.lang Require Export semantics.

From mizzle.stdlib Require Import rand.
From mizzle.logic Require Import interp goal goal_proof goal_tactics.

(** * Append-only trace library

    A simplified port of [iris.heap_lang.lib.trace] adapted for MizzleLang.
    Each trace entry is a pair [(τ, v)] of a [positive] label and a MizzleLang
    value. The on-heap encoding mirrors the original — [§TNone] for the
    empty trace, [‘TCons(τ, v, rest)] otherwise — and each operation
    acquires a spin lock at field [tlock] before reading or writing the
    [data] cell, so concurrent emits/lookups don't race.

    Clients see traces only through the abstract predicate [is_trace l
    ts] (sealed below) and the goal-mode helpers
    [goal_new_trace] / [goal_trace_emit] / [goal_trace_lookup] /
    [goal_trace_fresh], which expose each operation as a single step
    that consumes and produces [is_trace]. *)

(** ** Tag and field notations *)

Notation "'TNone'" :=
  (in_type "stdlib.trace.cell" 0)
  (in custom mizzle_tag).
Notation "'TCons'" :=
  (in_type "stdlib.trace.cell" 1)
  (in custom mizzle_tag).
Notation "'TRACE'" :=
  (in_type "stdlib.trace.trace" 0)
  (in custom mizzle_tag).
Notation "'data'" :=
  0
  (in custom mizzle_field).
Notation "'tlock'" :=
  1
  (in custom mizzle_field).

(** ** Lock primitives *)

Definition try_acquire : val := vfun: "l" => CAS "l".[tlock] false true.

Definition acquire : val :=
  vrec: "loop" "l" =>
    if: (try_acquire "l") then () else ("loop" "l").

Definition release : val := vfun: "l" => "l" <-{tlock} false.

(** ** Trace operations *)

Definition new_trace : val := vfun: <> => ‘TRACE{ §TNone, false }.

Definition trace_emit : val := vfun: "l" "τ" "v" =>
  acquire "l" ;;
  "l" <-{data} ‘TCons( "τ", "v", "l".{data} ) ;;
  release "l".

Definition trace_lookup : val := vfun: "l" =>
  acquire "l" ;;
  let: "t" := "l".{data} in
  release "l" ;;
  "t".

(** [trace_eq t1 t2] structurally compares two trace values. Each cell
    stores [‘TCons(τ, (kind, arg), rest)] — the label [τ] (a positive
    encoded as [ValInt]) and an event pair of two unboxed values. We
    destructure the event pair and compare the components separately,
    because [Equal] on a multi-field [Nongenerative] block is not a pure
    step (and is in fact forbidden). *)
Definition trace_eq : val :=
  vrec: "trace_eq" "t1" "t2" =>
    match: "t1" with
    | TNone =>
        match: "t2" with
        | TNone => true
        | TCons <> <> <> => false
        end
    | TCons "τ1" "v1" "rest1" =>
        match: "t2" with
        | TNone => false
        | TCons "τ2" "v2" "rest2" =>
            if: "τ1" == "τ2" then
              let: "k1", "a1" := "v1" in
              let: "k2", "a2" := "v2" in
              if: "k1" == "k2" then
                if: "a1" == "a2" then "trace_eq" "rest1" "rest2"
                else false
              else false
            else false
        end
    end.

(** [max_id t] returns a [positive] upper bound on the labels appearing
    in trace [t] — concretely the largest such label, or [1] if the
    trace is empty. *)
Definition max_id : val :=
  vrec: "max_id" "t" =>
    match: "t" with
    | TNone => 1
    | TCons "τ" <> "rest" =>
        let: "r" := "max_id" "rest" in
        if: "τ" ≤ "r" then "r" else "τ"
    end.

(** [is_fresh t id] returns [true] iff [id] does not occur as a label
    in trace [t]. *)
Definition is_fresh : val :=
  vrec: "is_fresh" "t" "id" =>
    match: "t" with
    | TNone => true
    | TCons "τ" <> "rest" =>
        if: "τ" == "id" then false else ("is_fresh" "rest" "id")
    end.

(** [nondet_nat ()] returns an arbitrary [nat], encoded by repeated
    [nondet_bool] calls (first as a stop bit, then bit-by-bit). *)
Definition nondet_nat : val :=
  vrec: "self" <> =>
    if: nondet_bool () then
      0
    else
      ((if: nondet_bool () then 1 else 0) + ("self" () * 2)).

(** [nondet_pos ()] returns an arbitrary [positive] (i.e., [≥ 1]). *)
Definition nondet_pos : val := vfun: <> => 1 + nondet_nat ().

(** [trace_fresh l v] picks a fresh label [τ] not occurring in the
    current trace and emits [(τ, v)], returning [τ]. Implementation:
    propose a non-deterministic positive [τ_p] via [nondet_pos]; if it
    happens to be fresh, use it, otherwise fall back to [max_id t + 1]
    (which is always fresh). The non-deterministic path lets Mizzle
    proofs drive [τ] to any caller-chosen fresh label (see
    [goal_trace_fresh_at]); the [max_id] fallback gives the deterministic
    [goal_trace_fresh] spec for callers that don't care which τ they
    receive. *)
Definition trace_fresh : val := vfun: "l" "v" =>
  acquire "l" ;;
  let: "t"   := "l".{data} in
  let: "τ_p" := nondet_pos () in
  let: "τ"   := if: is_fresh "t" "τ_p" then "τ_p" else (max_id "t" + 1) in
  "l" <-{data} ‘TCons( "τ", "v", "t" ) ;;
  release "l" ;;
  "τ".

(** ** Trace encoding *)

Fixpoint encode_trace (ts : list (positive * val)) : val :=
  match ts with
  | []           => §TNone%V
  | (τ, v) :: ts => ‘TCons( ValInt (Z.pos τ), v, encode_trace ts )%V
  end.

Section trace.
Context `{seqlogGS Σ}.

(** ** Abstract trace predicate *)

Definition is_trace_def (l : location) (ts : list (positive * val)) : iProp Σ :=
  l ↦ₕ□ Header (in_type "stdlib.trace.trace" 0) 2 ∗
  (l +ₗ 0) ↦ encode_trace ts ∗
  (l +ₗ 1) ↦ ValBool false.
Definition is_trace_aux : seal is_trace_def. Proof. by eexists. Qed.
Definition is_trace := is_trace_aux.(unseal).
Definition is_trace_unseal : is_trace = is_trace_def := is_trace_aux.(seal_eq).

Global Instance is_trace_timeless l ts : Timeless (is_trace l ts).
Proof. rewrite is_trace_unseal /is_trace_def. apply _. Qed.

(** ** Lock specs (internal helpers)

    The lock is field [tlock] of the trace location [l]. *)

Local Lemma goal_acquire E p ks (l : location) dqh tag :
  l ↦ₕ{dqh} Header tag 2 -∗
  (l +ₗ 1) ↦ ValBool false -∗
  focused p ks (acquire (ValLoc l)) -∗
  (l ↦ₕ{dqh} Header tag 2 -∗ (l +ₗ 1) ↦ ValBool true -∗ focused p ks (Val ValUnit) -∗ goal E) -∗
  goal E.
Proof.
  iIntros "Hhdr Hl Hp Hcont". rewrite /acquire.
  g_call "Hp". rewrite /try_acquire.
  g_call "Hp".
  g_block "Hp".
  g_cas_succ_cell "Hp" "Hhdr" "Hl".
  iSimpl in "Hl". iSimpl in "Hp".
  g_if_true "Hp".
  iApply ("Hcont" with "Hhdr Hl Hp").
Qed.

Local Lemma goal_release E p ks (l : location) (b : bool) dqh tag :
  l ↦ₕ{dqh} Header tag 2 -∗
  (l +ₗ 1) ↦ ValBool b -∗
  focused p ks (release (ValLoc l)) -∗
  (l ↦ₕ{dqh} Header tag 2 -∗ (l +ₗ 1) ↦ ValBool false -∗ focused p ks (Val ValUnit) -∗ goal E) -∗
  goal E.
Proof.
  iIntros "Hhdr Hl Hp Hcont". rewrite /release.
  g_call "Hp". g_set_field_cell "Hp" "Hhdr" "Hl".
  iApply ("Hcont" with "Hhdr Hl Hp").
Qed.

(** ** Maximum-label spec (internal) *)

Local Lemma goal_max_id E p ks (ts : list (positive * val)) :
  focused p ks (max_id (encode_trace ts)) -∗
  (∀ τ : positive,
    ⌜Forall (λ x, (x ≤ τ)%positive) ts.*1⌝ -∗
    focused p ks (Val (ValInt (Z.pos τ))) -∗ goal E) -∗
  goal E.
Proof.
  iIntros "Hp Hcont".
  iInduction ts as [|[τ v] ts IH] forall (ks).
  - simpl. rewrite {1}/max_id.
    g_call "Hp".
    g_pure (Match _ _ _ _) "Hp".
    iApply ("Hcont" $! 1%positive with "[%] Hp").
    by apply Forall_nil.
  - simpl. iEval (rewrite /max_id) in "Hp".
    g_call "Hp".
    g_pure (Match _ _ _ _) "Hp".
    iEval (fold max_id) in "Hp".
    g_focus (max_id _) "Hp".
    iApply ("IH" with "Hp"). iIntros (τ_rest Hbound) "Hp". simpl.
    g_let "Hp". g_binop "Hp".
    destruct (Z.le_gt_cases (Z.pos τ) (Z.pos τ_rest)) as [Hle | Hgt].
    + rewrite (bool_decide_eq_true_2 _ Hle). g_if_true "Hp". simpl.
      iApply ("Hcont" $! τ_rest with "[%] Hp").
      apply Forall_cons; split; [lia|done].
    + rewrite (bool_decide_eq_false_2 _); [|lia]. g_if_false "Hp". simpl.
      iApply ("Hcont" $! τ with "[%] Hp").
      apply Forall_cons; split; first lia.
      eapply Forall_impl; first done. simpl. lia.
Qed.

(** ** Non-deterministic positive integer specs (internal helpers) *)

Local Opaque nondet_bool.

Local Lemma goal_nondet_nat E p ks (n : nat) :
  focused p ks (nondet_nat ())%E -∗
  (focused p ks (Val (ValInt (Z.of_nat n))) -∗ goal E) -∗
  goal E.
Proof.
  iIntros "Hp Hcont".
  iInduction n as [n IHn] using (well_founded_induction Wf_nat.lt_wf)
    forall (ks).
  iEval (rewrite /nondet_nat) in "Hp". g_call "Hp".
  g_focus (nondet_bool _) "Hp".
  destruct (decide (n = 0%nat)) as [-> | Hne].
  { iApply (goal_rand _ _ _ true with "Hp"). iIntros "Hp". iSimpl in "Hp".
    g_if_true "Hp". }
  iApply (goal_rand _ _ _ false with "Hp"). iIntros "Hp". iSimpl in "Hp".
  g_if_false "Hp".
  g_focus (nondet_nat _) "Hp".
  iApply ("IHn" $! (n / 2)%nat with "[%] Hp"); first by apply Nat.div_lt; lia.
  iIntros "Hp". iSimpl in "Hp". g_binop "Hp".
  g_focus (nondet_bool _) "Hp".
  destruct (Nat.odd n) eqn:Hodd.
  + iApply (goal_rand _ _ _ true with "Hp"). iIntros "Hp". iSimpl in "Hp".
    g_if_true "Hp". g_binop "Hp".
    iApply ("Hcont" with "[Hp]").
    replace (1 + Z.of_nat (Nat.divmod n 1 0 1).1 * 2)%Z with (Z.of_nat n);
      [iExact "Hp"|].
    apply Nat.odd_spec, Nat.Odd_double in Hodd.
    rewrite Nat.div2_div in Hodd.
    change ((n `div` 2)%nat) with ((Nat.divmod n 1 0 1).1) in Hodd. lia.
  + iApply (goal_rand _ _ _ false with "Hp"). iIntros "Hp". iSimpl in "Hp".
    g_if_false "Hp". g_binop "Hp".
    iApply ("Hcont" with "[Hp]").
    replace (0 + Z.of_nat (Nat.divmod n 1 0 1).1 * 2)%Z with (Z.of_nat n);
      [iExact "Hp"|].
    assert (Nat.even n = true) as Heven by (rewrite -Nat.negb_odd Hodd //).
    apply Nat.even_spec, Nat.Even_double in Heven.
    rewrite Nat.div2_div in Heven.
    change ((n `div` 2)%nat) with ((Nat.divmod n 1 0 1).1) in Heven. lia.
Qed.

Local Lemma goal_nondet_pos E p ks (n : positive) :
  focused p ks (nondet_pos ())%E -∗
  (focused p ks (Val (ValInt (Z.pos n))) -∗ goal E) -∗
  goal E.
Proof.
  iIntros "Hp Hcont". rewrite /nondet_pos.
  g_call "Hp".
  g_focus (nondet_nat _) "Hp".
  iApply (goal_nondet_nat _ _ _ (Pos.to_nat n - 1)%nat with "Hp"). iIntros "Hp".
  iSimpl in "Hp". g_binop "Hp".
  iApply ("Hcont" with "[Hp]").
  replace (1 + Z.of_nat (Pos.to_nat n - 1))%Z with (Z.pos n) by lia.
  iExact "Hp".
Qed.

(** ** Freshness check spec (internal) *)

Local Lemma goal_is_fresh E p ks (ts : list (positive * val)) (τ : positive) :
  focused p ks (is_fresh (encode_trace ts) (ValInt (Z.pos τ))) -∗
  (focused p ks (Val (ValBool (bool_decide (τ ∉ ts.*1)))) -∗ goal E) -∗
  goal E.
Proof.
  iIntros "Hp Hcont".
  iInduction ts as [|[τ' v'] ts IH] forall (ks); simpl.
  - iEval (rewrite /is_fresh) in "Hp".
    g_call2 "Hp".
    g_pure (Match _ _ _ _) "Hp".
  - iEval (rewrite /is_fresh) in "Hp".
    g_call2 "Hp".
    g_pure (Match _ _ _ _) "Hp".
    g_equal "Hp".
    destruct (decide (τ' = τ)) as [-> | Hne].
    + rewrite (bool_decide_eq_true_2 (Z.pos τ = Z.pos τ)); [|done].
      g_if_true "Hp".
      rewrite (bool_decide_eq_false_2 (τ ∉ τ :: ts.*1)); [|set_solver].
      iApply ("Hcont" with "Hp").
    + rewrite (bool_decide_eq_false_2 (Z.pos τ' = Z.pos τ));
        [|by injection 1; lia].
      g_if_false "Hp".
      iEval (fold is_fresh) in "Hp".
      iApply ("IH" with "Hp"). iIntros "Hp".
      case_bool_decide as Hin.
      * rewrite (bool_decide_eq_true_2 (τ ∉ τ' :: ts.*1)); [|set_solver].
        iApply ("Hcont" with "Hp").
      * rewrite (bool_decide_eq_false_2 (τ ∉ τ' :: ts.*1)); [|set_solver].
        iApply ("Hcont" with "Hp").
Qed.

Lemma goal_new_trace E p ks :
  focused p ks (new_trace ())%E -∗
  (∀ l : location, is_trace l [] -∗ focused p ks (Val (ValLoc l)) -∗ goal E) -∗
  goal E.
Proof.
  iIntros "Hp Hcont". rewrite /new_trace.
  g_call "Hp".
  iApply (goal_block_mutable _ _ _ _ [§TNone%V; ValBool false] with "Hp");
    first (simpl; lia).
  iIntros (l) "Hhdr Hcells Hp". simpl.
  iDestruct "Hcells" as "(Hl & Hlock & _)".
  iApply ("Hcont" with "[Hhdr Hl Hlock] Hp").
  rewrite is_trace_unseal /is_trace_def.
  iFrame.
Qed.

Lemma goal_trace_emit E p ks (l : location) (τ : positive) (v : val)
    (ts : list (positive * val)) :
  is_trace l ts -∗
  focused p ks (trace_emit (ValLoc l) (ValInt (Z.pos τ)) v) -∗
  (is_trace l ((τ, v) :: ts) -∗ focused p ks (Val ValUnit) -∗ goal E) -∗
  goal E.
Proof.
  rewrite is_trace_unseal /is_trace_def.
  iIntros "(Hhdr & Hl & Hlock) Hp Hcont". rewrite /trace_emit.
  g_call3 "Hp".
  g_focus (acquire _) "Hp".
  iApply (goal_acquire with "Hhdr Hlock Hp"). iIntros "Hhdr Hlock Hp". simpl.
  g_let "Hp".
  g_get_field_cell "Hp" "Hhdr" "Hl". g_pure (Block _ _ _) "Hp".
  g_set_field_cell "Hp" "Hhdr" "Hl".
  change (ValBlock Nongenerative (in_type "stdlib.trace.cell" 1)
            [ValInt (Z.pos τ); v; encode_trace ts])
    with (encode_trace ((τ, v) :: ts)).
  g_let "Hp".
  iApply (goal_release with "Hhdr Hlock Hp"). iIntros "Hhdr Hlock Hp".
  iApply ("Hcont" with "[Hhdr Hl Hlock] Hp"). iFrame.
Qed.

Lemma goal_trace_lookup E p ks (l : location) (ts : list (positive * val)) :
  is_trace l ts -∗
  focused p ks (trace_lookup (ValLoc l)) -∗
  (is_trace l ts -∗ focused p ks (Val (encode_trace ts)) -∗ goal E) -∗
  goal E.
Proof.
  rewrite is_trace_unseal /is_trace_def.
  iIntros "(Hhdr & Hl & Hlock) Hp Hcont". rewrite /trace_lookup.
  g_call "Hp".
  g_focus (acquire _) "Hp".
  iApply (goal_acquire with "Hhdr Hlock Hp"). iIntros "Hhdr Hlock Hp". simpl.
  g_let "Hp".
  g_get_field_cell "Hp" "Hhdr" "Hl". g_let "Hp".
  g_focus (release _) "Hp".
  iApply (goal_release with "Hhdr Hlock Hp"). iIntros "Hhdr Hlock Hp". simpl.
  g_let "Hp".
  iApply ("Hcont" with "[Hhdr Hl Hlock] Hp"). iFrame.
Qed.

Lemma goal_trace_fresh_at E p ks (l : location) (v : val)
    (ts : list (positive * val)) (τ : positive) :
  τ ∉ ts.*1 →
  is_trace l ts -∗
  focused p ks (trace_fresh (ValLoc l) v) -∗
  (is_trace l ((τ, v) :: ts) -∗
   focused p ks (Val (ValInt (Z.pos τ))) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hfresh).
  rewrite is_trace_unseal /is_trace_def.
  iIntros "(Hhdr & Hl & Hlock) Hp Hcont". rewrite /trace_fresh.
  g_call2 "Hp".
  g_focus (acquire _) "Hp".
  iApply (goal_acquire with "Hhdr Hlock Hp"). iIntros "Hhdr Hlock Hp". simpl.
  g_let "Hp".
  g_get_field_cell "Hp" "Hhdr" "Hl". g_let "Hp".
  g_focus (nondet_pos _) "Hp".
  iApply (goal_nondet_pos _ _ _ τ with "Hp"). iIntros "Hp". iSimpl in "Hp".
  g_let "Hp".
  g_focus (is_fresh _ _) "Hp".
  iApply (goal_is_fresh _ with "Hp"). iIntros "Hp". iSimpl in "Hp".
  rewrite (bool_decide_eq_true_2 _ Hfresh).
  g_if_true "Hp". g_let "Hp".
  g_pure (Block _ _ _) "Hp".
  g_set_field_cell "Hp" "Hhdr" "Hl".
  change (ValBlock Nongenerative (in_type "stdlib.trace.cell" 1)
            [ValInt (Z.pos τ); v; encode_trace ts])
    with (encode_trace ((τ, v) :: ts)).
  g_let "Hp".
  g_focus (release _) "Hp".
  iApply (goal_release with "Hhdr Hlock Hp"). iIntros "Hhdr Hlock Hp". simpl.
  g_let "Hp".
  iApply ("Hcont" with "[Hhdr Hl Hlock] Hp"). iFrame.
Qed.

Lemma goal_trace_fresh E p ks (l : location) (v : val)
    (ts : list (positive * val)) :
  is_trace l ts -∗
  focused p ks (trace_fresh (ValLoc l) v) -∗
  (∀ τ : positive,
    ⌜τ ∉ ts.*1⌝ -∗
    is_trace l ((τ, v) :: ts) -∗
    focused p ks (Val (ValInt (Z.pos τ))) -∗ goal E) -∗
  goal E.
Proof.
  iIntros "Htr Hp Hcont".
  iApply (goal_trace_fresh_at _ _ _ _ _ (fresh ts.*1) with "Htr Hp");
    first apply infinite_is_fresh.
  iIntros "Htr Hp".
  iApply ("Hcont" with "[%] Htr Hp"). apply infinite_is_fresh.
Qed.

(** ** Trace equality spec *)

(** Predicate: [v] is a 2-tuple of two integer literals.

    This matches the "kind/arg" trace events used by clients (see
    [test/hw1_traced.v]), and ensures that the per-component [Equal] checks in
    [trace_eq] reduce as pure steps via [pure_equal_int]. The more
    permissive [val_immediate] doesn't suffice because [Equal] on, e.g.,
    two empty [Nongenerative] blocks isn't deterministic. *)
Definition is_pair_of_ints (v : val) : Prop :=
  ∃ (a b : Z), v = (ValInt a, ValInt b)%V.

Lemma goal_trace_eq E p ks (ts1 ts2 : list (positive * val)) :
  Forall (λ x, is_pair_of_ints x.2) ts1 →
  Forall (λ x, is_pair_of_ints x.2) ts2 →
  focused p ks (trace_eq (encode_trace ts1) (encode_trace ts2)) -∗
  (focused p ks (Val (ValBool (bool_decide (ts1 = ts2)))) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hu1 Hu2) "Hp Hcont".
  iInduction ts1 as [|[τ1 v1] ts1 IH] forall (ts2 ks Hu2).
  { destruct ts2 as [|[τ2 v2] ts2]; simpl;
      iEval (rewrite /trace_eq) in "Hp";
      g_call2 "Hp";
      g_pure (Match _ _ _ _) "Hp";
      g_pure (Match _ _ _ _) "Hp";
      iApply ("Hcont" with "Hp"). }
  apply Forall_cons in Hu1 as [Hv1 Hu1]. simpl in Hv1.
  destruct Hv1 as (a1 & b1 & ->).
  destruct ts2 as [|[τ2 v2] ts2]; simpl.
  { iEval (rewrite /trace_eq) in "Hp".
    g_call2 "Hp".
    g_pure (Match _ _ _ _) "Hp".
    g_pure (Match _ _ _ _) "Hp". }
  apply Forall_cons in Hu2 as [Hv2 Hu2]. simpl in Hv2.
  destruct Hv2 as (a2 & b2 & ->).
  iEval (rewrite /trace_eq) in "Hp".
  g_call2 "Hp".
  g_pure (Match _ _ _ _) "Hp".
  g_pure (Match _ _ _ _) "Hp".
  g_equal "Hp".
  destruct (decide (τ1 = τ2)) as [-> | Hne_τ];
    [|rewrite (bool_decide_eq_false_2 (Z.pos τ1 = Z.pos τ2)); [|by injection 1; lia];
      g_if_false "Hp";
      rewrite (bool_decide_eq_false_2
        ((τ1, (ValInt a1, ValInt b1)%V)%core :: ts1
         = (τ2, (ValInt a2, ValInt b2)%V)%core :: ts2));
        [|by intros [=]];
      iApply ("Hcont" with "Hp")].
  rewrite (bool_decide_eq_true_2 (Z.pos τ2 = Z.pos τ2)); [|done].
  g_if_true "Hp".
  g_pure (Match _ _ _ _) "Hp".
  g_pure (Match _ _ _ _) "Hp".
  g_equal "Hp".
  destruct (decide (a1 = a2)) as [-> | Hne_a];
    [|rewrite (bool_decide_eq_false_2 (a1 = a2)); [|done];
      g_if_false "Hp";
      rewrite (bool_decide_eq_false_2
        ((τ2, (ValInt a1, ValInt b1)%V)%core :: ts1
         = (τ2, (ValInt a2, ValInt b2)%V)%core :: ts2));
        [|by intros [= ?]];
      iApply ("Hcont" with "Hp")].
  rewrite (bool_decide_eq_true_2 (a2 = a2)); [|done].
  g_if_true "Hp".
  g_equal "Hp".
  destruct (decide (b1 = b2)) as [-> | Hne_b];
    [|rewrite (bool_decide_eq_false_2 (b1 = b2)); [|done];
      g_if_false "Hp";
      rewrite (bool_decide_eq_false_2
        ((τ2, (ValInt a2, ValInt b1)%V)%core :: ts1
         = (τ2, (ValInt a2, ValInt b2)%V)%core :: ts2));
        [|by intros [= ?]];
      iApply ("Hcont" with "Hp")].
  rewrite (bool_decide_eq_true_2 (b2 = b2)); [|done].
  g_if_true "Hp".
  iApply ("IH" with "[//] [//] Hp"). iIntros "Hp".
  destruct (decide (ts1 = ts2)) as [-> | Hne];
    [rewrite (bool_decide_eq_true_2 (ts2 = ts2)); [|done];
     rewrite (bool_decide_eq_true_2
       ((τ2, (ValInt a2, ValInt b2)%V)%core :: ts2
        = (τ2, (ValInt a2, ValInt b2)%V)%core :: ts2)); [|done];
     iApply ("Hcont" with "Hp")
    |rewrite (bool_decide_eq_false_2 (ts1 = ts2)); [|done];
     rewrite (bool_decide_eq_false_2
       ((τ2, (ValInt a2, ValInt b2)%V)%core :: ts1
        = (τ2, (ValInt a2, ValInt b2)%V)%core :: ts2));
       [|by intros [=]];
     iApply ("Hcont" with "Hp")].
Qed.

End trace.

Global Opaque is_trace.
