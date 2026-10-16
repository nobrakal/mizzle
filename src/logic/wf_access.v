From stdpp Require Import relations.
From mizzle.lang Require Import semantics.

From mizzle.logic Require Import decompose.

(** [wf_access σ e]: the next redex of [e] (as identified by [decompose])
    is not an out-of-bounds field access against [σ]'s headers. Vacuous
    on every redex shape other than the mutable field operations. *)
Definition wf_access (σ : state) (e : expr) : Prop :=
  match (decompose e).2 with
  | GetField  _ (Val (ValLoc l)) (Val (ValInt fld))
  | SetField _ (Val (ValLoc l)) (Val (ValInt fld)) (Val _) =>
      ∃ hdr, σ.(state_headers) !! l = Some hdr ∧
             (0 ≤ fld < Z.of_nat (header_size hdr))%Z
  | Xchg (Val (ValTuple [ValLoc l; ValInt fld])) (Val _)
  | CAS  (Val (ValTuple [ValLoc l; ValInt fld])) (Val _) (Val _)
  | FAA  (Val (ValTuple [ValLoc l; ValInt fld])) (Val (ValInt _)) =>
      ∃ hdr, σ.(state_headers) !! l = Some hdr ∧
             (0 ≤ fld < Z.of_nat (header_size hdr))%Z
  | _ => True
  end.

(** Extract [wf_access σ] on the redex itself from the per-thread invariant. *)
Lemma wf_access_at_redex σ es tid K e :
  es !! tid = Some (fill K e) →
  Forall (wf_access σ) es →
  to_val e = None →
  decompose_step e = None →
  wf_access σ e.
Proof.
  intros Hl HF Hv Hd.
  pose proof (Forall_lookup_1 _ _ _ _ HF Hl) as Hwa.
  unfold wf_access in Hwa |- *.
  rewrite (decompose_fill_redex K e Hv Hd) in Hwa.
  pose proof (decompose_fill_redex [] e Hv Hd) as Hde.
  change (fill [] e) with e in Hde.
  rewrite Hde.
  exact Hwa.
Qed.

(** Extract [wf_access σ] on the redex itself from a single [wf_access] on
    a filled expression — the per-step counterpart to [wf_access_at_redex]. *)
Lemma wf_access_fill σ K e :
  wf_access σ (fill K e) →
  to_val e = None →
  decompose_step e = None →
  wf_access σ e.
Proof.
  intros Hwa Hv Hd.
  unfold wf_access in Hwa |- *.
  rewrite (decompose_fill_redex K e Hv Hd) in Hwa.
  pose proof (decompose_fill_redex [] e Hv Hd) as Hde.
  change (fill [] e) with e in Hde.
  rewrite Hde.
  exact Hwa.
Qed.

(** [wf_access] only depends on the [decompose]-redex, so it agrees on a
    filled redex and the bare redex. *)
Lemma wf_access_fill_eq σ K e :
  to_val e = None →
  decompose_step e = None →
  wf_access σ (fill K e) = wf_access σ e.
Proof.
  intros Hv Hd. unfold wf_access.
  rewrite (decompose_fill_redex K e Hv Hd).
  pose proof (decompose_fill_redex [] e Hv Hd) as Hde.
  change (fill [] e) with e in Hde.
  rewrite Hde. reflexivity.
Qed.

(** A pure-step redex is never a field access, so [wf_access] holds
    vacuously: a field op's reducibility depends on the heap, hence cannot be
    pure. We refute the five field-op shapes of [(decompose (fill K e1)).2] by
    instantiating [pure_step_safe] at the empty heap. *)
Lemma pure_step_wf_access σ K e1 e2 :
  pure_step e1 e2 → wf_access σ (fill K e1).
Proof.
  intros Hps.
  (* [fill K e1] is not a value (it is reducible). *)
  assert (HvE : to_val (fill K e1) = None).
  { apply to_val_fill.
    destruct (pure_step_safe _ _ Hps 0 σ) as (e' & σ' & es & Hp).
    eapply prim_step_not_val; eauto. }
  pose proof (decompose_redex_no_step (fill K e1)) as Hns.
  pose proof (decompose_redex_not_val (fill K e1) HvE) as Hnv.
  pose proof (decompose_sound (fill K e1)) as Hsound.
  unfold wf_access.
  destruct (decompose (fill K e1)) as [Kc r] eqn:Hdec. simpl in Hns, Hnv, Hsound |- *.
  (* [r] is base-reducible in every state. *)
  assert (Hredr : ∀ σ0, ∃ e2' σ2 es, base_step 0 r σ0 [] e2' σ2 es).
  { intros σ0.
    destruct (pure_step_safe _ _ Hps 0 σ0) as (e' & σ' & es & Hp).
    destruct Hp as [Kb eb eb' Heb Heb' Hbs].
    assert (HpE : prim_step 0 (fill K e1) σ0 [] (fill (Kb ++ K) eb') σ' es).
    { eapply (base_step_fill_prim_step' (Kb ++ K) eb eb').
      - rewrite fill_app. rewrite Heb. reflexivity.
      - reflexivity.
      - exact Hbs. }
    destruct HpE as [K' e1'' e2'' HK' He2'' Hbs'].
    assert (Heq : fill Kc r = fill K' e1'') by (rewrite Hsound; exact HK').
    destruct (step_by_val 0 Kc K' r e1'' σ0 [] e2'' σ' es Heq Hnv Hbs') as [K'' ->].
    rewrite fill_app in Heq. apply (fill_inj Kc) in Heq.
    destruct K'' as [|k K''0 _] using rev_ind.
    - simpl in Heq. subst r. eauto.
    - exfalso. rewrite fill_snoc in Heq.
      assert (Hv0 : to_val (fill K''0 e1'') = None)
        by (apply to_val_fill; eapply base_step_not_val; eauto).
      rewrite Heq in Hns.
      rewrite (decompose_step_filli k (fill K''0 e1'') Hv0) in Hns.
      discriminate. }
  (* Case on the redex. For the five field-op constructors, invert the
     empty-heap base step: it refines the redex to a concrete shape. Immutable
     (block) reads reduce the goal to [True]; the genuine mutable field ops
     leave an empty-heap lookup premise, which is contradictory. *)
  destruct r; try exact I;
    destruct (Hredr {| state_headers := ∅; state_heap := ∅;
                       state_locals := [] |})
      as (? & ? & ? & Hbs);
    inversion Hbs; subst; simpl in *; try exact I;
    repeat match goal with
    | H : is_Some _ |- _ => destruct H as [? H]
    | H : _ !! _ = Some _ |- _ => rewrite lookup_empty in H
    end;
    discriminate.
Qed.

(** [silent_step] refined so the thread actually being reduced performs a
    well-formed (in-bounds) field access, with the observation trace [κ]
    emitted by the primitive step made explicit. Per-step: the constraint
    bears only on the reduced redex, not the whole pool. *)
Definition step (ρ1 : list expr * state)
    (o : list observation) (ρ2 : list expr * state) : Prop :=
  ∃ κ tid e1 e2 σ2 efs,
    prim_step tid e1 ρ1.2 κ e2 σ2 efs ∧
    ρ1.1 !! tid = Some e1 ∧
    ρ2 = (<[tid := e2]> ρ1.1 ++ efs, σ2) ∧
    wf_access ρ1.2 e1 ∧
    o = κ.

(** Irreducibility w.r.t. [step]: [e] cannot perform any in-bounds
    ([wf_access]) primitive step. Weaker than [irreducible]: a genuinely
    out-of-bounds redex is [irreducible_no_oob] vacuously, since no
    [wf_access] step exists. *)
Definition irreducible_no_oob tid e σ :=
  ∀ κ e' σ' es, prim_step tid e σ κ e' σ' es → wf_access σ e → False.

Lemma irreducible_irreducible_no_oob tid e σ :
  irreducible tid e σ → irreducible_no_oob tid e σ.
Proof. intros Hir κ e' σ' es Hstep _. by eapply Hir. Qed.

Lemma step_silent_step ρ1 o ρ2 :
  step ρ1 o ρ2 → silent_step ρ1 ρ2.
Proof.
  intros (κ & tid & e1 & e2 & σ2 & efs & Hp & Hl & Heq & _ & _).
  exists κ, tid, e1, e2, σ2, efs. done.
Qed.

(** Reflexive-transitive closure that accumulates the observation trace. *)
Inductive traced_steps :
    (list expr * state) → list observation → (list expr * state) → Prop :=
  | traced_steps_refl ρ : traced_steps ρ [] ρ
  | traced_steps_l ρ1 o ρ2 os ρ3 :
     step ρ1 o ρ2 →
     traced_steps ρ2 os ρ3 →
     traced_steps ρ1 (o ++ os) ρ3.

Lemma construct_step_fill es σ p ks e e' σ' :
  es !! p = Some (fill ks e) →
  base_step p e σ [] e' σ' [] →
  wf_access σ (fill ks e) →
  step (es, σ) [] (<[p:=fill ks e']> es, σ').
Proof.
  intros Hlook Hstep Hwa.
  exists [], p, (fill ks e), (fill ks e'), σ', [].
  rewrite app_nil_r. split_and!; try done.
  econstructor; [reflexivity|reflexivity|exact Hstep].
Qed.

Lemma traced_steps_rtc_silent_step ρ1 κ ρ2 :
  traced_steps ρ1 κ ρ2 → rtc silent_step ρ1 ρ2.
Proof.
  induction 1 as [|ρ1 κ ρ2 κs ρ3 Hstep _ IH]; first done.
  eapply rtc_l; last exact IH.
  by eapply step_silent_step.
Qed.
