(** * Decidable linearizability check ************************************

    Generic boolean check for [trace_linearizable] over a model that has
    an executable [step] function. Strategy:

    1. From a trace [ts] (with [Call]/[Ret] events), determine the unique
       [Lin] event for each tag with both a [Call] and a [Ret] (same
       request as the [Call], same result as the [Ret]).

    2. Enumerate all permutations of these [Lin] events. For each, run
       [linearized_sound_check] (recursive function calling [step]).

    3. If no permutation succeeds, the trace is not linearizable
       (soundness lemma; converse not needed).

    The class is split in two so the function-only [executable_model] can
    stay transparent (needed for [vm_compute] over its [step] projection)
    while the proof-only [executable_model_correct] can be opaque (Qed
    or Admitted) without blocking computation. *)

From stdpp Require Import ssreflect.
From stdpp Require Import relations gmap list list_monad.

From mizzle.lang Require Import semantics.

From mizzle.pure_logic Require Import linear.

(** ** Executable refinement (function only) *****************************

    Stays transparent. *)
Class executable_model `{M : model} := {
  step : S → val → val → option S;
}.

(** ** Soundness of [step] vs [request_response] (proofs only) ***********

    Can be opaque. *)
Class executable_model_correct `{M : model} `{em : !@executable_model M} := {
  step_sound s req res s' :
    @step M em s req res = Some s' →
    valid_request req ∧ request_response s req s' res;
  step_complete s req res s' :
    valid_request req →
    request_response s req s' res →
    @step M em s req res = Some s';
}.

(** ** Lin events implied by a trace's Call/Ret pairs ********************

    Walk [ts] left-to-right. Each [Call(τ, v)] is recorded; when we
    later see [Ret(τ, v')], emit [(τ, Lin v v')]. *)

Fixpoint lins_of_trace_aux (ts : list (positive * trace))
    (calls : gmap positive val) : list (positive * trace) :=
  match ts with
  | [] => []
  | (τ, Call v) :: rest =>
      lins_of_trace_aux rest (<[τ:=v]> calls)
  | (τ, Lin _ _) :: rest =>
      lins_of_trace_aux rest calls
  | (τ, Ret v') :: rest =>
      match calls !! τ with
      | Some v => (τ, Lin v v') :: lins_of_trace_aux rest (delete τ calls)
      | None => lins_of_trace_aux rest calls
      end
  end.

Definition lins_of_trace (ts : list (positive * trace))
  : list (positive * trace) :=
  lins_of_trace_aux ts ∅.

(** ** Permutations *******************************************************

    We use stdpp's [permutations] function, which produces all
    permutations of a list. The lemma [permutations_Permutation] connects
    [_ ∈ permutations xs] to the [Permutation] (multiset-equivalence)
    relation. *)

(** ** [linearized_sound] check *******************************************)

Section sound_check.
  Context `{M : model} `{!@executable_model M}.

  Fixpoint linearized_sound_check (lins : list (positive * trace))
      (s : S) : bool :=
    match lins with
    | [] => true
    | (_, Lin v v') :: rest =>
        match step s v v' with
        | Some s' => linearized_sound_check rest s'
        | None => false
        end
    | _ :: _ => false
    end.
End sound_check.

(** ** [linearized_sound_check] vs [linearized_sound] *********************

    Soundness/completeness of the boolean check against the inductive
    [linearized_sound] Prop. Both directions need [executable_model_correct]
    to invoke [step_sound] / [step_complete]. *)

Section sound_check_correct.
  Context `{M : model} `{em : !@executable_model M, !@executable_model_correct M em}.

  Lemma linearized_sound_check_sound lins s :
    linearized_sound_check lins s = true →
    ∃ s', linearized_sound lins s s'.
  Proof.
    revert s. induction lins as [|[τ [v|v v'|v]] rest IH]; intros s Hcheck.
    - exists s. apply linearized_sound_nil.
    - cbn in Hcheck. discriminate.
    - cbn in Hcheck. destruct (step s v v') as [s_mid|] eqn:Hstep; last discriminate.
      apply step_sound in Hstep as [Hvalid Hrr].
      destruct (IH _ Hcheck) as [s' Hsound].
      exists s'. by eapply linearized_sound_cons.
    - cbn in Hcheck. discriminate.
  Qed.

  Lemma linearized_sound_check_complete lins s s' :
    linearized_sound lins s s' →
    linearized_sound_check lins s = true.
  Proof.
    revert s s'.
    induction lins as [|[τ et] rest IH]; intros s s' Hsound.
    - cbn. done.
    - destruct et as [v|v v'|v].
      + exfalso. apply linearized_sound_is_lin in Hsound.
        rewrite Forall_cons in Hsound. cbn in Hsound. tauto.
      + apply linearized_sound_cons_inv in Hsound
          as (s_mid & Hvalid & Hrr & Hrest).
        cbn. erewrite step_complete by eauto.
        eapply IH; eassumption.
      + exfalso. apply linearized_sound_is_lin in Hsound.
        rewrite Forall_cons in Hsound. cbn in Hsound. tauto.
  Qed.
End sound_check_correct.

(** ** Top-level check ****************************************************)

(** ** Real-time precedence ************************************************

    Without filtering, [is_linearizable_check] would consider permutations
    that don't correspond to any valid [ts'] — e.g., a [Lin Enq 2] coming
    after a [Lin Deq 1] when in [ts] the [Ret] of [Enq 2] precedes the
    [Call] of [Deq 1]. To get a usable check we filter to permutations
    respecting the real-time partial order: if [(τ, Ret _)] appears
    before [(τ', Call _)] in [ts], the corresponding [Lin τ] must
    precede [Lin τ'] in σ. *)

(** Position of the [Lin] event with the given tag in σ. *)
Fixpoint lin_position (σ : list (positive * trace)) (τ : positive) : option nat :=
  match σ with
  | [] => None
  | (τ', Lin _ _) :: rest =>
      if decide (τ = τ') then Some 0%nat
      else option_map Datatypes.S (lin_position rest τ)
  | _ :: rest => option_map Datatypes.S (lin_position rest τ)
  end.

(** Precedence pairs: collect [(τ, τ')] such that [(τ, Ret _)] appears
    before [(τ', Call _)] in [ts]. *)
Fixpoint rt_pairs_aux (ts : list (positive * trace))
    (rets_seen : list positive) : list (positive * positive) :=
  match ts with
  | [] => []
  | (τ, Ret _) :: rest => rt_pairs_aux rest (τ :: rets_seen)
  | (τ, Call _) :: rest =>
      ((λ ρ, (ρ, τ)) <$> rets_seen) ++ rt_pairs_aux rest rets_seen
  | _ :: rest => rt_pairs_aux rest rets_seen
  end.

Definition rt_pairs (ts : list (positive * trace))
  : list (positive * positive) :=
  rt_pairs_aux ts [].

Definition rt_pair_respected (σ : list (positive * trace))
    (p : positive * positive) : bool :=
  let '(τ, τ') := p in
  match lin_position σ τ, lin_position σ τ' with
  | Some i, Some j => bool_decide (i < j)%nat
  | _, _ => true (* missing Lin: vacuously OK *)
  end.

Definition respects_rt (ts σ : list (positive * trace)) : bool :=
  forallb (rt_pair_respected σ) (rt_pairs ts).

Section check.
  Context `{M : model} `{!@executable_model M}.

  Definition is_linearizable_check (ts : list (positive * trace)) : bool :=
    existsb (λ σ, respects_rt ts σ && linearized_sound_check σ s_init)
            (permutations (lins_of_trace ts)).
End check.

(** ** Soundness of the top-level check ***********************************

    [is_linearizable_check ts = false → ¬ trace_linearizable ts] under the
    precondition that every tag in [ts] appears as a [Call+Ret] pair (or
    not at all). Pending operations (Call without Ret) are ruled out by
    [per_tag_complete]. *)

(** *** Positional helpers for [rt_pairs] and [filter] *********************)

(** [rt_pairs_aux] characterization: [(ρ, τ)] is in the output iff some
    [(τ, Call _)] event sits at index [i_C], and either [ρ] was already
    in [rets_seen] or some [(ρ, Ret _)] event sits at an earlier index. *)
Lemma rt_pairs_aux_in_iff ts ρ τ :
  ∀ rets_seen,
    (ρ, τ) ∈ rt_pairs_aux ts rets_seen ↔
    ∃ i_C v_C, ts !! i_C = Some (τ, Call v_C) ∧
      (ρ ∈ rets_seen ∨
       ∃ i_R v_R, (i_R < i_C)%nat ∧ ts !! i_R = Some (ρ, Ret v_R)).
Proof.
  induction ts as [|[τ' [v|v v'|v]] rest IH] => rets_seen.
  - cbn. split.
    + by intros []%elem_of_nil.
    + intros (i_C & v_C & Hi & _). by destruct i_C.
  - (* Call v :: rest *)
    cbn. rewrite elem_of_app. split.
    + intros [Hin | Hin].
      * (* (ρ, τ) came from [map (λ ρ', (ρ', τ')) rets_seen]: τ' = τ, ρ ∈ rets_seen *)
        apply list_elem_of_fmap (* y ∈ f <$> l ↔ ∃ x, y = f x ∧ x ∈ l *) in Hin as (ρ' & Heq & Hρ').
        injection Heq as -> ->.
        exists 0%nat, v. by auto.
      * apply IH in Hin as (i_C & v_C & Hi & Hor).
        exists (Datatypes.S i_C), v_C. cbn. split; first done.
        destruct Hor as [Hρ | (i_R & v_R & Hlt & Hi_R)]; first by left.
        right. exists (Datatypes.S i_R), v_R. cbn. split; [lia | done].
    + intros (i_C & v_C & Hi & Hor).
      destruct i_C as [|i_C']; cbn in Hi.
      * (* Call event at position 0 *)
        injection Hi as -> ->.
        destruct Hor as [Hρ | (i_R & v_R & Hlt & _)]; last lia.
        left. apply list_elem_of_fmap (* y ∈ f <$> l ↔ ∃ x, y = f x ∧ x ∈ l *). by exists ρ.
      * right. apply IH. exists i_C', v_C. split; first done.
        destruct Hor as [Hρ | (i_R & v_R & Hlt & Hi_R)]; first by left.
        destruct i_R as [|i_R']; cbn in Hi_R; first discriminate.
        right. exists i_R', v_R. split; [lia | done].
  - (* Lin v v' :: rest *)
    cbn. rewrite IH. split.
    + intros (i_C & v_C & Hi & Hor).
      exists (Datatypes.S i_C), v_C. cbn. split; first done.
      destruct Hor as [Hρ | (i_R & v_R & Hlt & Hi_R)]; first by left.
      right. exists (Datatypes.S i_R), v_R. cbn. split; [lia | done].
    + intros (i_C & v_C & Hi & Hor).
      destruct i_C as [|i_C']; cbn in Hi; first discriminate.
      exists i_C', v_C. split; first done.
      destruct Hor as [Hρ | (i_R & v_R & Hlt & Hi_R)]; first by left.
      destruct i_R as [|i_R']; cbn in Hi_R; first discriminate.
      right. exists i_R', v_R. split; [lia | done].
  - (* Ret v :: rest *)
    cbn. rewrite IH. split.
    + intros (i_C & v_C & Hi & Hor).
      exists (Datatypes.S i_C), v_C. cbn. split; first done.
      destruct Hor as [Hρ | (i_R & v_R & Hlt & Hi_R)].
      * (* ρ ∈ τ' :: rets_seen: either ρ = τ' (matched by Ret at 0) or ρ ∈ rets_seen. *)
        apply elem_of_cons in Hρ as [-> | Hρ].
        -- right. exists 0%nat, v. cbn. split; [lia | done].
        -- by left.
      * right. exists (Datatypes.S i_R), v_R. cbn. split; [lia | done].
    + intros (i_C & v_C & Hi & Hor).
      destruct i_C as [|i_C']; cbn in Hi; first discriminate.
      exists i_C', v_C. split; first done.
      destruct Hor as [Hρ | (i_R & v_R & Hlt & Hi_R)].
      * left. by apply elem_of_cons; right.
      * destruct i_R as [|i_R']; cbn in Hi_R.
        -- (* Ret event at position 0 was (τ', Ret v): so ρ = τ' *)
           injection Hi_R as -> _.
           left. by apply elem_of_cons; left.
        -- right. exists i_R', v_R. split; [lia | done].
Qed.

(** Specialization of [rt_pairs_aux_in_iff] to [rt_pairs] (initial empty
    [rets_seen]). *)
Lemma rt_pairs_in_iff ts ρ τ :
  (ρ, τ) ∈ rt_pairs ts ↔
  ∃ i_R i_C v_R v_C,
    ts !! i_R = Some (ρ, Ret v_R) ∧
    ts !! i_C = Some (τ, Call v_C) ∧
    (i_R < i_C)%nat.
Proof.
  unfold rt_pairs. rewrite rt_pairs_aux_in_iff. split.
  - intros (i_C & v_C & Hi & [Hρ%elem_of_nil | (i_R & v_R & Hlt & HR)]); first done.
    by exists i_R, i_C, v_R, v_C.
  - intros (i_R & i_C & v_R & v_C & HR & HC & Hlt).
    exists i_C, v_C. split; first done.
    right. by exists i_R, v_R.
Qed.

(** Filter preserves order: if two distinct positions in [filter P l]
    contain elements [x] and [y], then they map to two distinct positions
    in [l] (in the same order). *)
Lemma filter_lookup_lift {A} (P : A → Prop) `{∀ x, Decision (P x)}
    (l : list A) (i j : nat) (x y : A) :
  filter P l !! i = Some x →
  filter P l !! j = Some y →
  (i < j)%nat →
  ∃ i' j', l !! i' = Some x ∧ l !! j' = Some y ∧ (i' < j')%nat.
Proof.
  revert i j x y.
  induction l as [|h l IH] => i j x y Hi Hj Hij.
  - rewrite filter_nil /= in Hi. discriminate.
  - rewrite filter_cons in Hi Hj.
    case_decide as Hh.
    + (* P h *) destruct i as [|i'].
      * cbn in Hi. injection Hi as ->.
        destruct j as [|j']; first lia. cbn in Hj.
        (* Need to find y in l. *)
        (* j' has y in (filter P l), so by simpler lookup, y ∈ l at some index. *)
        assert (∃ j'', l !! j'' = Some y) as (j'' & Hj'').
        { revert Hj. clear. revert j'. induction l as [|h l IH] => j' Hj.
          - rewrite filter_nil /= in Hj. discriminate.
          - rewrite filter_cons in Hj. case_decide.
            + destruct j' as [|j'']; cbn in Hj.
              * injection Hj as ->. by exists 0%nat.
              * apply IH in Hj as (j''' & ?). by exists (Datatypes.S j''').
            + apply IH in Hj as (j''' & ?). by exists (Datatypes.S j'''). }
        exists 0%nat, (Datatypes.S j''). cbn. split_and!; [done|done|lia].
      * cbn in Hi.
        destruct j as [|j']; first lia. cbn in Hj.
        destruct (IH _ _ _ _ Hi Hj ltac:(lia)) as (i'' & j'' & Hi'' & Hj'' & Hlt).
        exists (Datatypes.S i''), (Datatypes.S j''). cbn. split_and!; [done|done|lia].
    + destruct (IH _ _ _ _ Hi Hj Hij) as (i'' & j'' & Hi'' & Hj'' & Hlt).
      exists (Datatypes.S i''), (Datatypes.S j''). cbn. split_and!; [done|done|lia].
Qed.

(** Inverse direction: if [l !! i = Some x], [P x], and [l !! j = Some y],
    [P y], with [i < j], then there exist [i' < j'] in [filter P l] with
    [filter P l !! i' = Some x] and [filter P l !! j' = Some y]. *)
Lemma filter_lookup_drop {A} (P : A → Prop) `{∀ x, Decision (P x)}
    (l : list A) (i j : nat) (x y : A) :
  l !! i = Some x →
  l !! j = Some y →
  P x → P y → (i < j)%nat →
  ∃ i' j', filter P l !! i' = Some x ∧ filter P l !! j' = Some y ∧ (i' < j')%nat.
Proof.
  revert i j x y.
  induction l as [|h l IH] => i j x y Hi Hj Hpx Hpy Hij.
  - cbn in Hi. discriminate.
  - destruct i as [|i'].
    + cbn in Hi. injection Hi as ->.
      destruct j as [|j']; first lia. cbn in Hj.
      (* Find y at some index in [filter P l]. *)
      assert (∃ j'', filter P l !! j'' = Some y) as (j'' & Hj'').
      { clear -Hj Hpy. revert j' Hj. induction l as [|h l IH] => j' Hj.
        - by destruct j'.
        - destruct j' as [|j''].
          + cbn in Hj. injection Hj as ->.
            rewrite filter_cons. case_decide; first by exists 0%nat.
            done.
          + cbn in Hj. apply IH in Hj as (j''' & ?).
            rewrite filter_cons. case_decide.
            * by exists (Datatypes.S j''').
            * by exists j'''. }
      rewrite filter_cons. case_decide; last done.
      exists 0%nat, (Datatypes.S j''). cbn. split_and!; [done|done|lia].
    + cbn in Hi.
      destruct j as [|j']; first lia. cbn in Hj.
      destruct (IH _ _ _ _ Hi Hj Hpx Hpy ltac:(lia)) as (i'' & j'' & Hi'' & Hj'' & Hlt).
      rewrite filter_cons. case_decide.
      * exists (Datatypes.S i''), (Datatypes.S j''). cbn. split_and!; [done|done|lia].
      * by exists i'', j''.
Qed.

(** *** [lin_position] characterization ***********************************)

Lemma lin_position_None_iff σ τ :
  lin_position σ τ = None ↔
  ∀ i v v', σ !! i ≠ Some (τ, Lin v v').
Proof.
  induction σ as [|[τ' [v0|v0 v0'|v0]] rest IH]; cbn.
  - split; first by intros _ [|]. done.
  - rewrite fmap_None IH. split.
    + intros Hnone i v v'. destruct i as [|i'].
      * cbn. by intros [= ->].
      * cbn. apply Hnone.
    + intros Hall i v v'. apply (Hall (Datatypes.S i)).
  - (* Lin v0 v0' *)
    case_decide as Hτ.
    + subst τ'. split; first done.
      intros Hall. exfalso. by apply (Hall 0%nat v0 v0').
    + rewrite fmap_None IH. split.
      * intros Hnone i v v'. destruct i as [|i'].
        -- cbn. intros [= -> ? ?]. by apply Hτ.
        -- cbn. apply Hnone.
      * intros Hall i v v'. apply (Hall (Datatypes.S i)).
  - rewrite fmap_None IH. split.
    + intros Hnone i v v'. destruct i as [|i'].
      * cbn. by intros [= ->].
      * cbn. apply Hnone.
    + intros Hall i v v'. apply (Hall (Datatypes.S i)).
Qed.

(** If [lin_position σ τ = Some i], then there exists a [(τ, Lin _ _)]
    at index [i] in σ, and no earlier [(τ, Lin _ _)] event in σ. *)
Lemma lin_position_Some_inv σ τ i :
  lin_position σ τ = Some i →
  ∃ v v', σ !! i = Some (τ, Lin v v') ∧
    ∀ j v_L v'_L, (j < i)%nat → σ !! j ≠ Some (τ, Lin v_L v'_L).
Proof.
  revert i. induction σ as [|[τ' [v0|v0 v0'|v0]] rest IH] => i Hpos; cbn in Hpos.
  - discriminate.
  - apply fmap_Some in Hpos as (i' & Hpos & ->).
    apply IH in Hpos as (v & v' & Hi & Hbefore).
    exists v, v'. split.
    + cbn. exact Hi.
    + intros j v_L v'_L Hj. destruct j as [|j']; cbn.
      * by intros [= ->].
      * apply Hbefore. lia.
  - case_decide as Hτ.
    + subst τ'. injection Hpos as <-.
      exists v0, v0'. split; first done. intros j v_L v'_L Hj. lia.
    + apply fmap_Some in Hpos as (i' & Hpos & ->).
      apply IH in Hpos as (v & v' & Hi & Hbefore).
      exists v, v'. split.
      * cbn. exact Hi.
      * intros j v_L v'_L Hj. destruct j as [|j']; cbn.
        -- by intros [= -> ? ?].
        -- apply Hbefore. lia.
  - apply fmap_Some in Hpos as (i' & Hpos & ->).
    apply IH in Hpos as (v & v' & Hi & Hbefore).
    exists v, v'. split.
    + cbn. exact Hi.
    + intros j v_L v'_L Hj. destruct j as [|j']; cbn.
      * by intros [= ->].
      * apply Hbefore. lia.
Qed.

(** Converse: a [(τ, Lin _ _)] at index [i] in σ with no earlier such event
    pins down [lin_position σ τ = Some i]. *)
Lemma lin_position_Some σ τ i v v' :
  σ !! i = Some (τ, Lin v v') →
  (∀ j v_L v'_L, (j < i)%nat → σ !! j ≠ Some (τ, Lin v_L v'_L)) →
  lin_position σ τ = Some i.
Proof.
  revert i. induction σ as [|[τ' [v0|v0 v0'|v0]] rest IH] => i Hi Hbefore;
    first by destruct i.
  - destruct i as [|i']; cbn in Hi; first discriminate.
    cbn. rewrite (IH i'); auto.
    intros j v_L v'_L Hj. apply (Hbefore (Datatypes.S j) v_L v'_L). lia.
  - cbn. case_decide as Hτ.
    + subst τ'. destruct i as [|i'].
      * cbn in Hi. by injection Hi as -> ->.
      * exfalso. specialize (Hbefore 0%nat v0 v0' ltac:(lia)). by apply Hbefore.
    + destruct i as [|i'].
      * cbn in Hi. injection Hi as ->. by exfalso.
      * cbn. rewrite (IH i'); auto.
        intros j v_L v'_L Hj. apply (Hbefore (Datatypes.S j) v_L v'_L). lia.
  - destruct i as [|i']; cbn in Hi; first discriminate.
    cbn. rewrite (IH i'); auto.
    intros j v_L v'_L Hj. apply (Hbefore (Datatypes.S j) v_L v'_L). lia.
Qed.

(** *** Per-tag positional ordering from [per_tag_linearized] *************)

(** If [(τ, Lin v v')] appears at index [j] in [ts'], then in any segment
    of [ts'] before [j], no [(τ, Ret _)] can appear (Lin is before Ret in
    the per-tag order). Symmetrically: after [j], no [(τ, Call _)]. *)

(** Concretely: the positional consequence we need for [respects_rt]. *)
Lemma per_tag_linearized_lin_ret_order ts' τ j_L k_R v_L v'_L v_R :
  per_tag_linearized ts' →
  ts' !! j_L = Some (τ, Lin v_L v'_L) →
  ts' !! k_R = Some (τ, Ret v_R) →
  (j_L < k_R)%nat.
Proof.
  intros Hper Hj_L Hk_R.
  destruct (decide (j_L < k_R)%nat) as [Hlt | Hge]; first done. exfalso.
  apply not_lt in Hge.
  destruct (decide (j_L = k_R)) as [-> | Hne].
  { rewrite Hj_L in Hk_R. discriminate. }
  assert (Hkj : (k_R < j_L)%nat) by lia.
  destruct (filter_lookup_drop (λ t : positive*trace, t.1 = τ) ts'
              k_R j_L (τ, Ret v_R) (τ, Lin v_L v'_L)
              Hk_R Hj_L eq_refl eq_refl Hkj)
    as (i_R' & i_L' & Hi_R' & Hi_L' & Hlt').
  destruct (Hper τ) as (v0 & v0' & Hpref).
  apply (prefix_lookup_Some _ _ _ _ Hi_R') in Hpref as Hpref_R.
  apply (prefix_lookup_Some _ _ _ _ Hi_L') in Hpref as Hpref_L.
  destruct i_R' as [|[|[|i_R'']]]; cbn in Hpref_R; try discriminate.
  destruct i_L' as [|[|[|i_L'']]]; cbn in Hpref_L; try discriminate; lia.
Qed.

Lemma per_tag_linearized_call_lin_order ts' τ k_C j_L v_C v_L v'_L :
  per_tag_linearized ts' →
  ts' !! k_C = Some (τ, Call v_C) →
  ts' !! j_L = Some (τ, Lin v_L v'_L) →
  (k_C < j_L)%nat.
Proof.
  intros Hper Hk_C Hj_L.
  destruct (decide (k_C < j_L)%nat) as [Hlt | Hge]; first done. exfalso.
  apply not_lt in Hge.
  destruct (decide (k_C = j_L)) as [-> | Hne].
  { rewrite Hk_C in Hj_L. discriminate. }
  assert (Hkj : (j_L < k_C)%nat) by lia.
  destruct (filter_lookup_drop (λ t : positive*trace, t.1 = τ) ts'
              j_L k_C (τ, Lin v_L v'_L) (τ, Call v_C)
              Hj_L Hk_C eq_refl eq_refl Hkj)
    as (i_L' & i_C' & Hi_L' & Hi_C' & Hlt').
  destruct (Hper τ) as (v0 & v0' & Hpref).
  apply (prefix_lookup_Some _ _ _ _ Hi_L') in Hpref as Hpref_L.
  apply (prefix_lookup_Some _ _ _ _ Hi_C') in Hpref as Hpref_C.
  destruct i_L' as [|[|[|i_L'']]]; cbn in Hpref_L; try discriminate.
  destruct i_C' as [|[|[|i_C'']]]; cbn in Hpref_C; try discriminate; lia.
Qed.

Lemma per_tag_linearized_call_ret_order ts' τ k_C k_R v_C v_R :
  per_tag_linearized ts' →
  ts' !! k_C = Some (τ, Call v_C) →
  ts' !! k_R = Some (τ, Ret v_R) →
  (k_C < k_R)%nat.
Proof.
  intros Hper Hk_C Hk_R.
  destruct (decide (k_C < k_R)%nat) as [Hlt | Hge]; first done. exfalso.
  apply not_lt in Hge.
  destruct (decide (k_C = k_R)) as [-> | Hne].
  { rewrite Hk_C in Hk_R. discriminate. }
  assert (Hkj : (k_R < k_C)%nat) by lia.
  destruct (filter_lookup_drop (λ t : positive*trace, t.1 = τ) ts'
              k_R k_C (τ, Ret v_R) (τ, Call v_C)
              Hk_R Hk_C eq_refl eq_refl Hkj)
    as (i_R' & i_C' & Hi_R' & Hi_C' & Hlt').
  destruct (Hper τ) as (v0 & v0' & Hpref).
  apply (prefix_lookup_Some _ _ _ _ Hi_R') in Hpref as Hpref_R.
  apply (prefix_lookup_Some _ _ _ _ Hi_C') in Hpref as Hpref_C.
  destruct i_R' as [|[|[|i_R'']]]; cbn in Hpref_R; try discriminate.
  destruct i_C' as [|[|[|i_C'']]]; cbn in Hpref_C; try discriminate; lia.
Qed.

(** *** Helpers for the multiset sub-lemma ********************************)

(** A [(τ, Lin v v')] pair can sit at only one index in [ts']. *)
Lemma per_tag_linearized_unique_lin ts' τ v v' k1 k2 :
  per_tag_linearized ts' →
  ts' !! k1 = Some (τ, Lin v v') →
  ts' !! k2 = Some (τ, Lin v v') →
  k1 = k2.
Proof.
  intros Hper H1 H2.
  assert (Hcontra : ∀ a b, ts' !! a = Some (τ, Lin v v') →
                           ts' !! b = Some (τ, Lin v v') →
                           (a < b)%nat → False).
  { intros a b Ha Hb Hab.
    destruct (filter_lookup_drop (λ t : positive*trace, t.1 = τ) ts' a b _ _
                Ha Hb eq_refl eq_refl Hab) as (i1 & i2 & Hi1 & Hi2 & Hii).
    destruct (Hper τ) as (v0 & v0' & Hpref).
    apply (prefix_lookup_Some _ _ _ _ Hi1) in Hpref as Hpref1.
    apply (prefix_lookup_Some _ _ _ _ Hi2) in Hpref as Hpref2.
    destruct i1 as [|[|[|]]]; cbn in Hpref1; try discriminate.
    destruct i2 as [|[|[|]]]; cbn in Hpref2; try discriminate; lia. }
  destruct (Nat.lt_total k1 k2) as [Hlt | [Heq | Hgt]].
  - exfalso. eapply (Hcontra k1 k2 H1 H2 Hlt).
  - exact Heq.
  - exfalso. eapply (Hcontra k2 k1 H2 H1 Hgt).
Qed.

(** [filter (is_lin ∘ snd) ts'] is duplicate-free. *)
Lemma filter_is_lin_NoDup ts' :
  per_tag_linearized ts' →
  NoDup (filter (is_lin ∘ snd) ts').
Proof.
  intros Hper. apply NoDup_alt. intros i j x Hi Hj.
  assert (Hx : ∃ τ v v', x = (τ, Lin v v')).
  { apply list_elem_of_lookup_2, list_elem_of_filter in Hi as [Hlin _].
    destruct x as [τ [v|v v'|v]]; cbn in Hlin; try done. by eauto. }
  destruct Hx as (τ & v & v' & ->).
  destruct (Nat.lt_total i j) as [Hlt | [Heq | Hgt]]; [|done|].
  - exfalso.
    destruct (filter_lookup_lift (is_lin ∘ snd) ts' i j _ _ Hi Hj Hlt)
      as (k_i & k_j & Hk_i & Hk_j & Hk_lt).
    pose proof (per_tag_linearized_unique_lin _ _ _ _ _ _ Hper Hk_i Hk_j). lia.
  - exfalso.
    destruct (filter_lookup_lift (is_lin ∘ snd) ts' j i _ _ Hj Hi Hgt)
      as (k_j & k_i & Hk_j & Hk_i & Hk_lt).
    pose proof (per_tag_linearized_unique_lin _ _ _ _ _ _ Hper Hk_j Hk_i). lia.
Qed.

(** [lins_of_trace_aux] only emits [Lin] events. *)
Lemma lins_of_trace_aux_is_lin ts calls x :
  x ∈ lins_of_trace_aux ts calls → is_lin x.2.
Proof.
  revert calls.
  induction ts as [|[τ' [v|v v'|v]] rest IH] => calls Hin; cbn in Hin.
  - by apply elem_of_nil in Hin.
  - by apply IH in Hin.
  - by apply IH in Hin.
  - destruct (calls !! τ') as [v_call|] eqn:Hcall.
    + apply elem_of_cons in Hin as [-> | Hin]; first done.
      by apply IH in Hin.
    + by apply IH in Hin.
Qed.

(** Tag membership in [(lins_of_trace_aux ts calls).*1] requires either
    [calls !! τ ≠ None] or a [Call τ] event in [ts]. Useful contrapositive:
    if [filter (.1=τ) ts = []] and [calls !! τ = None], the output has no
    [(τ, _)] entry. *)
Lemma lins_of_trace_aux_tag_origin ts calls τ :
  τ ∈ (lins_of_trace_aux ts calls).*1 →
  calls !! τ ≠ None ∨ ∃ i v, ts !! i = Some (τ, Call v).
Proof.
  revert calls.
  induction ts as [|[τ' [v|v v'|v]] rest IH] => calls Hin; cbn in Hin.
  - by apply elem_of_nil in Hin.
  - apply IH in Hin as [Hcalls | (i & v_C & Hi)].
    + destruct (decide (τ = τ')) as [-> | Hne].
      * right. exists 0%nat, v. cbn. done.
      * left. by rewrite lookup_insert_ne in Hcalls.
    + right. by exists (Datatypes.S i), v_C.
  - apply IH in Hin as [Hcalls | (i & v_C & Hi)].
    + by left.
    + right. by exists (Datatypes.S i), v_C.
  - destruct (calls !! τ') as [v_call|] eqn:Hcall.
    + (* Hin: τ ∈ ((τ', Lin v_call v) :: rec).*1 = τ' :: rec.*1 *)
      cbn in Hin. apply elem_of_cons in Hin as [-> | Hin].
      * left. by rewrite Hcall.
      * apply IH in Hin as [Hcalls | (i & v_C & Hi)].
        -- destruct (decide (τ = τ')) as [-> | Hne].
           ++ left. by rewrite Hcall.
           ++ left. by rewrite lookup_delete_ne in Hcalls.
        -- right. by exists (Datatypes.S i), v_C.
    + apply IH in Hin as [Hcalls | (i & v_C & Hi)]; first by left.
      right. by exists (Datatypes.S i), v_C.
Qed.

(** A useful corollary: if [filter (.1=τ) ts = []] and [calls !! τ = None],
    no entry in [(lins_of_trace_aux ts calls).*1] equals [τ]. *)
Lemma lins_of_trace_aux_no_tag ts calls τ :
  filter (λ t : positive*trace, t.1 = τ) ts = [] →
  calls !! τ = None →
  τ ∉ (lins_of_trace_aux ts calls).*1.
Proof.
  intros Hfilt Hcalls Hin.
  apply lins_of_trace_aux_tag_origin in Hin as [|(i & v_C & Hi)]; first done.
  apply list_elem_of_lookup_2 in Hi.
  assert ((τ, Call v_C) ∈ filter (λ t : positive*trace, t.1 = τ) ts) as Hbad
    by (apply list_elem_of_filter; by split).
  rewrite Hfilt in Hbad. by apply elem_of_nil in Hbad.
Qed.

(** Calls-invariant: each tag's filter is constrained by whether the tag
    is "live" in [calls] (Call already consumed) or "fresh" (no Call yet). *)
Definition calls_inv (ts : list (positive * trace)) (calls : gmap positive val) : Prop :=
  ∀ τ,
    match calls !! τ with
    | None =>
        filter (λ t : positive*trace, t.1 = τ) ts = [] ∨
        ∃ v v', filter (λ t, t.1 = τ) ts = [(τ, Call v); (τ, Ret v')]
    | Some _ =>
        filter (λ t : positive*trace, t.1 = τ) ts = [] ∨
        ∃ v', filter (λ t, t.1 = τ) ts = [(τ, Ret v')]
    end.

Lemma per_tag_complete_calls_inv_init ts :
  per_tag_complete ts → calls_inv ts ∅.
Proof.
  intros Hc τ. rewrite lookup_empty.
  destruct (Hc τ) as (v & v' & [Heq | Heq]).
  - by left.
  - right. by exists v, v'.
Qed.

(** [calls_inv] is preserved by stepping past [Call τ_h v_h] and inserting
    into [calls]. *)
Lemma calls_inv_step_call ts τ_h v_h calls :
  calls_inv ((τ_h, Call v_h) :: ts) calls →
  calls_inv ts (<[τ_h:=v_h]> calls).
Proof.
  intros Hinv τ. specialize (Hinv τ).
  destruct (decide (τ = τ_h)) as [-> | Hne].
  - rewrite lookup_insert_eq.
    rewrite filter_cons_True in Hinv; last done.
    destruct (calls !! τ_h) as [v|] eqn:Hcalls.
    + (* Old: filter ((τ_h,Call v_h)::ts) (.1=τ_h) ∈ {[], [Ret _]}.
         But head is (τ_h, Call v_h), so filter starts with Call. Contradiction. *)
      destruct Hinv as [Hbad | (v' & Hbad)]; discriminate.
    + destruct Hinv as [Hbad | (v_C & v_R & Heq)]; first discriminate.
      injection Heq as -> Heq_rest. by right; exists v_R.
  - rewrite lookup_insert_ne; last done.
    rewrite filter_cons_False in Hinv; last by cbn; intros ?; subst.
    exact Hinv.
Qed.

(** Stepping past [Lin τ_h _ _] preserves [calls_inv] only if [calls_inv]
    rules out a [Lin] event for [τ_h] — which it does, as the filter shapes
    contain no [Lin]. *)
Lemma calls_inv_step_lin ts τ_h v_h v_h' calls :
  calls_inv ((τ_h, Lin v_h v_h') :: ts) calls →
  calls_inv ts calls.
Proof.
  intros Hinv τ. specialize (Hinv τ).
  destruct (decide (τ = τ_h)) as [-> | Hne].
  - rewrite filter_cons_True in Hinv; last done.
    destruct (calls !! τ_h) as [v|] eqn:Hcalls.
    + destruct Hinv as [Hbad | (v' & Hbad)]; discriminate.
    + destruct Hinv as [Hbad | (v_C & v_R & Heq)]; discriminate.
  - rewrite filter_cons_False in Hinv; last by cbn; intros ?; subst.
    exact Hinv.
Qed.

(** Stepping past a [Ret τ_h v_h'] when [calls !! τ_h = Some v]: delete from
    calls. *)
Lemma calls_inv_step_ret_some ts τ_h v_h' v_h calls :
  calls_inv ((τ_h, Ret v_h') :: ts) calls →
  calls !! τ_h = Some v_h →
  calls_inv ts (delete τ_h calls).
Proof.
  intros Hinv Hcalls τ. specialize (Hinv τ).
  destruct (decide (τ = τ_h)) as [-> | Hne].
  - rewrite lookup_delete_eq.
    rewrite Hcalls in Hinv. rewrite filter_cons_True in Hinv; last done.
    destruct Hinv as [Hbad | (v_R & Heq)]; first discriminate.
    injection Heq as -> Heq_rest. by left.
  - rewrite lookup_delete_ne; last done.
    rewrite filter_cons_False in Hinv; last by cbn; intros ?; subst.
    exact Hinv.
Qed.

(** Under [calls_inv], a [Ret τ_h] event can only occur with [calls !! τ_h
    = Some _]; the [None] case contradicts the invariant. *)
Lemma calls_inv_ret_none_absurd ts τ_h v_h' calls :
  calls_inv ((τ_h, Ret v_h') :: ts) calls →
  calls !! τ_h = None →
  False.
Proof.
  intros Hinv Hcalls. specialize (Hinv τ_h).
  rewrite Hcalls in Hinv.
  rewrite filter_cons_True in Hinv; last done.
  destruct Hinv as [Hbad | (v_C & v_R & Heq)]; first discriminate.
  injection Heq as Heq_h _.
  discriminate.
Qed.

(** Under [calls_inv], a [Lin τ_h] event in [ts] is impossible. *)
Lemma calls_inv_no_lin ts τ_h v_h v_h' calls :
  calls_inv ((τ_h, Lin v_h v_h') :: ts) calls → False.
Proof.
  intros Hinv. specialize (Hinv τ_h).
  rewrite filter_cons_True in Hinv; last done.
  destruct (calls !! τ_h) as [v|];
    [destruct Hinv as [Hbad | (v_R & Hbad)] | destruct Hinv as [Hbad | (v_C & v_R & Hbad)]];
    discriminate.
Qed.

(** Tags-NoDup of [lins_of_trace_aux] under [calls_inv]. *)
Lemma lins_of_trace_aux_NoDup_tags ts calls :
  calls_inv ts calls →
  NoDup (lins_of_trace_aux ts calls).*1.
Proof.
  revert calls.
  induction ts as [|[τ' [v|v v'|v]] rest IH] => calls Hinv; cbn.
  - constructor.
  - apply IH, calls_inv_step_call. exact Hinv.
  - exfalso. by eapply calls_inv_no_lin.
  - destruct (calls !! τ') as [v_call|] eqn:Hcall.
    + cbn. constructor.
      * (* τ' ∉ tags of recursive output *)
        apply lins_of_trace_aux_no_tag.
        -- (* filter (.1=τ') rest = [] *)
           specialize (Hinv τ'). rewrite Hcall in Hinv.
           rewrite filter_cons_True in Hinv; last done.
           destruct Hinv as [Hbad | (v_R & Heq)]; first discriminate.
           injection Heq as -> Heq_rest. exact Heq_rest.
        -- by rewrite lookup_delete_eq.
      * apply IH. by eapply calls_inv_step_ret_some.
    + exfalso. by eapply calls_inv_ret_none_absurd.
Qed.

(** From tags-NoDup, NoDup of pairs follows. *)
Lemma lins_of_trace_aux_NoDup ts calls :
  calls_inv ts calls →
  NoDup (lins_of_trace_aux ts calls).
Proof.
  intros Hinv. eapply (NoDup_fmap_1 fst), lins_of_trace_aux_NoDup_tags, Hinv.
Qed.

Lemma lins_of_trace_NoDup ts :
  per_tag_complete ts → NoDup (lins_of_trace ts).
Proof.
  intros Hc. apply lins_of_trace_aux_NoDup, per_tag_complete_calls_inv_init, Hc.
Qed.

(** Membership characterization for [lins_of_trace_aux] output. Under
    [calls_inv], an entry [(τ, Lin v v')] sits in the output iff the
    [τ]-filter of [ts] has a definite shape that depends on whether
    [calls] already has [τ] live. *)
Lemma lins_of_trace_aux_lin_iff ts calls τ v v' :
  calls_inv ts calls →
  ((τ, Lin v v') ∈ lins_of_trace_aux ts calls ↔
   match calls !! τ with
   | None => filter (λ t : positive*trace, t.1 = τ) ts = [(τ, Call v); (τ, Ret v')]
   | Some v0 => v = v0 ∧ filter (λ t : positive*trace, t.1 = τ) ts = [(τ, Ret v')]
   end).
Proof.
  revert calls. induction ts as [|[τ_h [v_h|v_h v_h'|v_h']] rest IH] => calls Hinv.
  - cbn. destruct (calls !! τ); split.
    + by intros []%elem_of_nil.
    + by intros [_ Hbad].
    + by intros []%elem_of_nil.
    + done.
  - (* Call v_h *)
    cbn [lins_of_trace_aux]. rewrite filter_cons.
    case_decide as Hτh.
    + (* τ_h = τ *) cbn in Hτh. subst τ_h.
      assert (Hcalls : calls !! τ = None).
      { specialize (Hinv τ).
        destruct (calls !! τ) eqn:E; last done.
        rewrite filter_cons_True // in Hinv.
        destruct Hinv as [Hbad | (v_R & Hbad)]; discriminate. }
      rewrite Hcalls.
      rewrite (IH _ (calls_inv_step_call _ _ _ _ Hinv)).
      rewrite lookup_insert_eq.
      split.
      * intros [-> Hfilt]. by rewrite Hfilt.
      * intros Heq. injection Heq as -> ->. by split.
    + (* τ_h ≠ τ *) cbn in Hτh.
      rewrite (IH _ (calls_inv_step_call _ _ _ _ Hinv)).
      rewrite lookup_insert_ne; last by intros ->.
      done.
  - (* Lin: impossible under calls_inv *)
    exfalso. by eapply calls_inv_no_lin.
  - (* Ret v_h' *)
    cbn [lins_of_trace_aux].
    destruct (calls !! τ_h) as [v_h|] eqn:Hcalls_h; last first.
    { (* None: contradicts calls_inv *)
      exfalso. by eapply calls_inv_ret_none_absurd. }
    pose proof (calls_inv_step_ret_some _ _ _ _ _ Hinv Hcalls_h) as Hinv'.
    pose proof (IH _ Hinv') as IH'.
    rewrite elem_of_cons.
    rewrite filter_cons. case_decide as Hτh.
    + (* τ_h = τ *) cbn in Hτh. subst τ_h.
      rewrite Hcalls_h.
      rewrite IH' lookup_delete_eq.
      assert (Hfilt_rest : filter (λ t : positive*trace, t.1 = τ) rest = []).
      { specialize (Hinv τ). rewrite Hcalls_h filter_cons_True // in Hinv.
        destruct Hinv as [Hbad | (v_R & Heq)]; first discriminate.
        injection Heq as -> Heq_rest. exact Heq_rest. }
      rewrite Hfilt_rest.
      split.
      * intros [Heq | Hbad]; first (injection Heq as -> ->; by split).
        discriminate.
      * intros [-> Heq]. injection Heq as ->. by left.
    + (* τ_h ≠ τ *) cbn in Hτh.
      rewrite IH' lookup_delete_ne; last by intros ->.
      split.
      * intros [Heq | Hrhs]; first (injection Heq as Hbad; by exfalso).
        exact Hrhs.
      * intros Hrhs. by right.
Qed.

(** Helper: rewrite filter of filter using commutativity of predicates. *)
Lemma filter_outer_inner (ts' : list (positive * trace)) τ :
  filter (λ t : positive*trace, t.1 = τ) (filter (not ∘ is_lin ∘ snd) ts')
  = filter (not ∘ is_lin ∘ snd) (filter (λ t : positive*trace, t.1 = τ) ts').
Proof.
  rewrite !list_filter_filter. apply list_filter_iff. tauto.
Qed.

(** Membership characterization for the [is_lin] side: under
    [per_tag_linearized] + [per_tag_complete (filter (not is_lin) ts')],
    each tag's filter has either no events or the full Call/Lin/Ret triple. *)
Lemma per_tag_lin_complete_shape ts' τ :
  per_tag_linearized ts' →
  per_tag_complete (filter (not ∘ is_lin ∘ snd) ts') →
  filter (λ t : positive*trace, t.1 = τ) ts' = [] ∨
  ∃ v v', filter (λ t : positive*trace, t.1 = τ) ts' =
    [(τ, Call v); (τ, Lin v v'); (τ, Ret v')].
Proof.
  intros Hper Hcomp.
  destruct (Hper τ) as (v0 & v0' & Hpref).
  destruct (Hcomp τ) as (v_c & v_r & Hcomp_τ).
  rewrite filter_outer_inner in Hcomp_τ.
  destruct Hpref as [k Hpref].
  remember (filter (λ t : positive*trace, t.1 = τ) ts') as fts eqn:Hfts.
  pose proof (f_equal length Hpref) as Hlen.
  rewrite length_app in Hlen. cbn in Hlen.
  destruct fts as [|h0 [|h1 [|h2 [|h3 ?]]]];
    cbn in Hlen; try lia.
  - by left.
  - (* length 1: h0 *)
    cbn in Hpref. injection Hpref as Hh0 _. subst h0.
    exfalso.
    rewrite filter_cons_True in Hcomp_τ;
      last by (cbv [compose]; cbn; intro Hbad; apply Hbad).
    rewrite filter_nil in Hcomp_τ.
    destruct Hcomp_τ as [Hbad | Hbad]; discriminate.
  - (* length 2: h0 h1 *)
    cbn in Hpref. injection Hpref as Hh0 Hh1 _. subst h0 h1.
    exfalso.
    rewrite filter_cons_True in Hcomp_τ;
      last by (cbv [compose]; cbn; intro Hbad; apply Hbad).
    rewrite filter_cons_False in Hcomp_τ;
      last by (cbv [compose]; cbn; intro Hbad; apply Hbad).
    rewrite filter_nil in Hcomp_τ.
    destruct Hcomp_τ as [Hbad | Hbad]; discriminate.
  - (* length 3: h0 h1 h2 — full *)
    cbn in Hpref. injection Hpref as Hh0 Hh1 Hh2 _.
    subst h0 h1 h2. right. by exists v0, v0'.
Qed.

(** Membership equivalence sub-claim: each side has the same elements. *)
Lemma filter_is_lin_membership_iff ts' x :
  per_tag_complete (filter (not ∘ is_lin ∘ snd) ts') →
  per_tag_linearized ts' →
  x ∈ filter (is_lin ∘ snd) ts' ↔
  x ∈ lins_of_trace (filter (not ∘ is_lin ∘ snd) ts').
Proof.
  intros Hcomp Hper.
  destruct x as [τ [v|v v'|v]].
  - (* Call: not in filter is_lin (predicate fails) *)
    split.
    + intros Hin%list_elem_of_filter. by destruct Hin as [Hbad _].
    + intros Hin%lins_of_trace_aux_is_lin. done.
  - (* Lin v v' *)
    rewrite list_elem_of_filter.
    pose proof (per_tag_complete_calls_inv_init _ Hcomp) as Hinv.
    pose proof (lins_of_trace_aux_lin_iff _ ∅ τ v v' Hinv) as Hiff.
    rewrite lookup_empty in Hiff. rewrite Hiff. clear Hiff.
    (* Now: is_lin (Lin v v').snd ∧ (τ, Lin v v') ∈ ts' ↔
            filter (.1=τ) (filter (not is_lin) ts') = [(τ, Call v); (τ, Ret v')] *)
    rewrite filter_outer_inner.
    split.
    + intros [_ Hin].
      (* by per_tag_lin_complete_shape, filter (.1=τ) ts' = full triple. *)
      destruct (per_tag_lin_complete_shape ts' τ Hper Hcomp)
        as [Hempty | (v0 & v0' & Hfull)].
      * exfalso.
        assert (Hbad : (τ, Lin v v') ∈ filter (λ t : positive*trace, t.1 = τ) ts')
          by (apply list_elem_of_filter; by split).
        rewrite Hempty in Hbad. by apply elem_of_nil in Hbad.
      * assert (Hin_filt : (τ, Lin v v') ∈ filter (λ t : positive*trace, t.1 = τ) ts').
        { apply list_elem_of_filter. by split. }
        rewrite Hfull in Hin_filt.
        rewrite !elem_of_cons in Hin_filt.
        destruct Hin_filt as [Heq | [Heq | [Heq | Hbad]]]; try discriminate;
          last (by apply elem_of_nil in Hbad).
        injection Heq as -> ->.
        rewrite Hfull.
        rewrite filter_cons_True; last by (cbv [compose]; cbn; tauto).
        rewrite filter_cons_False; last by (cbv [compose]; cbn; tauto).
        rewrite filter_cons_True; last by (cbv [compose]; cbn; tauto).
        by rewrite filter_nil.
    + intros Heq. split; first done.
      destruct (per_tag_lin_complete_shape ts' τ Hper Hcomp)
        as [Hempty | (v0 & v0' & Hfull)].
      * exfalso. rewrite Hempty in Heq.
        rewrite filter_nil in Heq. discriminate.
      * assert (Hcalc : filter (not ∘ is_lin ∘ snd)
                          (filter (λ t : positive*trace, t.1 = τ) ts')
                        = [(τ, Call v0); (τ, Ret v0')]).
        { rewrite Hfull.
          rewrite filter_cons_True; last by (cbv [compose]; cbn; tauto).
          rewrite filter_cons_False; last by (cbv [compose]; cbn; tauto).
          rewrite filter_cons_True; last by (cbv [compose]; cbn; tauto).
          by rewrite filter_nil. }
        rewrite Hcalc in Heq.
        injection Heq as Hv Hv'.
        assert ((τ, Lin v v') ∈ filter (λ t : positive*trace, t.1 = τ) ts') as Hin'.
        { rewrite Hfull. rewrite Hv Hv'. by repeat constructor. }
        by apply list_elem_of_filter in Hin' as [_ Hin'].
  - (* Ret: not in filter is_lin *)
    split.
    + intros Hin%list_elem_of_filter. by destruct Hin as [Hbad _].
    + intros Hin%lins_of_trace_aux_is_lin. done.
Qed.

(** Sub-lemma: [filter is_lin ts'] is a permutation of [lins_of_trace ts].
    Provable per-tag from [per_tag_linearized] + the filter equation. *)
Lemma filter_is_lin_multiset ts' :
  per_tag_complete (filter (not ∘ is_lin ∘ snd) ts') →
  per_tag_linearized ts' →
  filter (is_lin ∘ snd) ts'
    ≡ₚ lins_of_trace (filter (not ∘ is_lin ∘ snd) ts').
Proof.
  intros Hcomp Hper. apply NoDup_Permutation.
  - by apply filter_is_lin_NoDup.
  - by apply lins_of_trace_NoDup.
  - intros x. by apply filter_is_lin_membership_iff.
Qed.

(** Sub-lemma: [filter is_lin ts'] respects the real-time partial order
    derived from [filter (not is_lin) ts']. Provable from
    [per_tag_linearized] + positional reasoning on [ts']. *)
Lemma filter_is_lin_respects_rt ts' :
  per_tag_linearized ts' →
  respects_rt (filter (not ∘ is_lin ∘ snd) ts')
              (filter (is_lin ∘ snd) ts') = true.
Proof.
  intros Hper. unfold respects_rt.
  apply forallb_forall. intros [ρ τ] Hin.
  apply list_elem_of_In, rt_pairs_in_iff in Hin
    as (i_R & i_C & v_R & v_C & HR_filt & HC_filt & Hlt_filt).
  destruct (filter_lookup_lift (not ∘ is_lin ∘ snd) ts' i_R i_C
              (ρ, Ret v_R) (τ, Call v_C) HR_filt HC_filt Hlt_filt)
    as (j_R & j_C & HR & HC & Hlt).
  unfold rt_pair_respected.
  destruct (lin_position (filter (is_lin ∘ snd) ts') ρ) as [i_ρ|] eqn:Hpos_ρ; last done.
  destruct (lin_position (filter (is_lin ∘ snd) ts') τ) as [i_τ|] eqn:Hpos_τ; last done.
  apply bool_decide_eq_true_2.
  apply lin_position_Some_inv in Hpos_ρ as (v_ρ & v'_ρ & Hi_ρ & _).
  apply lin_position_Some_inv in Hpos_τ as (v_τ & v'_τ & Hi_τ & _).
  destruct (decide (i_ρ < i_τ)%nat) as [|Hge]; first done. exfalso.
  apply not_lt in Hge.
  destruct (decide (i_ρ = i_τ)) as [Hi_eq | Hne].
  { (* same Lin position in [filter is_lin ts'] forces ρ = τ;
       per_tag_linearized then orders Call ρ before Ret ρ in ts',
       contradicting [Hlt : j_R < j_C]. *)
    rewrite Hi_eq Hi_τ in Hi_ρ. injection Hi_ρ as -> _ _.
    pose proof (per_tag_linearized_call_ret_order _ _ _ _ _ _ Hper HC HR) as Hlt_RC.
    lia. }
  assert (Hi_τ_lt : (i_τ < i_ρ)%nat) by lia.
  destruct (filter_lookup_lift (is_lin ∘ snd) ts' i_τ i_ρ
              (τ, Lin v_τ v'_τ) (ρ, Lin v_ρ v'_ρ) Hi_τ Hi_ρ Hi_τ_lt)
    as (k_τ & k_ρ & Hk_τ & Hk_ρ & Hlt_τρ).
  pose proof (per_tag_linearized_lin_ret_order _ _ _ _ _ _ _ Hper Hk_ρ HR) as Hlt_LR.
  pose proof (per_tag_linearized_call_lin_order _ _ _ _ _ _ _ Hper HC Hk_τ) as Hlt_CL.
  lia.
Qed.

Section check_sound.
  Context `{M : model} `{em : !@executable_model M, !@executable_model_correct M em}.

  (** The executable checker is sound: [false] on a per-tag-complete trace
      refutes linearizability, decided by [vm_compute]. *)
  Theorem is_linearizable_check_sound ts :
    per_tag_complete ts →
    is_linearizable_check ts = false →
    ¬ trace_linearizable ts.
  Proof.
    intros Hcomplete Hcheck (Hcv & ts' & Hfilter & Hper & s' & Hsound).
    (* σ := filter is_lin ts'. *)
    set (σ := filter (is_lin ∘ snd) ts').
    (* σ is a permutation of [lins_of_trace ts]. *)
    assert (Hperm : σ ≡ₚ lins_of_trace ts).
    { rewrite Hfilter. apply filter_is_lin_multiset; rewrite -?Hfilter //. }
    (* σ ∈ permutations (lins_of_trace ts). *)
    apply Permutation_sym in Hperm.
    apply permutations_Permutation in Hperm.
    (* σ respects rt. *)
    assert (Hrt : respects_rt ts σ = true).
    { rewrite Hfilter. apply filter_is_lin_respects_rt, Hper. }
    (* σ linearizes_sound. *)
    assert (Hcheck_σ : linearized_sound_check σ s_init = true).
    { eapply linearized_sound_check_complete, Hsound. }
    (* existsb finds σ. *)
    unfold is_linearizable_check in Hcheck.
    apply not_true_iff_false in Hcheck. apply Hcheck.
    apply existsb_exists. exists σ. split.
    - by apply list_elem_of_In, Hperm.
    - by rewrite Hrt Hcheck_σ.
  Qed.

  (** Combined with [call_valid], the checker yields non-linearizability. [[card]] *)
  Theorem is_non_linearizable_check_sound ts :
    call_valid ts →
    per_tag_complete ts →
    is_linearizable_check ts = false →
    trace_non_linearizable ts.
  Proof.
    intros Hcv Hcomplete Hcheck. split; first done.
    by apply is_linearizable_check_sound.
  Qed.
End check_sound.
