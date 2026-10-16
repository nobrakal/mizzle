From stdpp Require Import relations.
From iris.proofmode Require Import base proofmode.

From mizzle.lang Require Import instances.

From mizzle.logic Require Import interp translate decompose wf_access completeness.

(** Companion to [wf_access] for ops whose [ValLoc] base must be a
    header base in [σ] for the source side to step: [Match], [GetTag],
    [GetSize], and the heap ops [GetField], [SetField], [Xchg], [CAS], [FAA]. *)
Definition wf_header (σ : state) (e : expr) : Prop :=
  match (decompose e).2 with
  | Match (Val (ValLit (LitLoc l))) _ _ _
  | GetTag (Val (ValLit (LitLoc l)))
  | GetSize (Val (ValLit (LitLoc l)))
  | GetField  _ (Val (ValLit (LitLoc l))) (Val (ValInt _))
  | SetField _ (Val (ValLit (LitLoc l))) (Val (ValInt _)) (Val _)
  | Xchg (Val (ValTuple [ValLit (LitLoc l); ValInt _])) (Val _)
  | CAS  (Val (ValTuple [ValLit (LitLoc l); ValInt _])) (Val _) (Val _)
  | FAA  (Val (ValTuple [ValLit (LitLoc l); ValInt _])) (Val (ValInt _)) =>
      is_Some (σ.(state_headers) !! l)
  | _ => True
  end.

Lemma wf_header_at_redex σ es tid K e :
  es !! tid = Some (fill K e) →
  Forall (wf_header σ) es →
  to_val e = None →
  decompose_step e = None →
  wf_header σ e.
Proof.
  intros Hl HF Hv Hd.
  pose proof (Forall_lookup_1 _ _ _ _ HF Hl) as Hwa.
  rewrite /wf_header in Hwa |- *.
  rewrite (decompose_fill_redex K e Hv Hd) in Hwa.
  rewrite (decompose_fill_redex [] e Hv Hd).
  exact Hwa.
Qed.

(** ** Block-base location invariant.

    Locations enter the program only via [Alloc]/[Block Mutable], which
    return [#l] for a fresh header base. So every literal location in
    code / locals / heap is in [dom σ.headers]; redex shapes with a
    [ValLoc] base ([Match]/[GetTag]/[GetSize] and [GetField]/[SetField]/[Xchg]/
    [CAS]/[FAA]) therefore always satisfy [wf_header]. *)

Section locs_in_headers.

Definition locs_state_in_headers (σ : state) : Prop :=
  Forall (λ v, locs_val v ⊆ dom σ.(state_headers)) σ.(state_locals) ∧
  map_Forall (λ _ v, locs_val v ⊆ dom σ.(state_headers)) σ.(state_heap).

Definition locs_expr_in_headers (σ : state) (e : expr) : Prop :=
  locs_expr e ⊆ dom σ.(state_headers).

Lemma state_alloc_headers_dom l hdr vs σ :
  dom (state_alloc l hdr vs σ).(state_headers) = {[l]} ∪ dom σ.(state_headers).
Proof. simpl. set_solver. Qed.

Lemma state_set_location_headers l v σ :
  (state_set_location l v σ).(state_headers) = σ.(state_headers).
Proof. done. Qed.

Lemma state_set_local_headers tid v σ :
  (state_set_local tid v σ).(state_headers) = σ.(state_headers).
Proof. done. Qed.

Lemma state_add_local_headers v σ :
  (state_add_local v σ).(state_headers) = σ.(state_headers).
Proof. done. Qed.

(** Per-redex preservation. Headers only grow, [e2]'s locations stay
    inside [σ2.headers], spawned threads inherit the bound, and the
    state invariant is maintained. *)
Lemma base_step_locs_in_headers tid e1 σ1 κ e2 σ2 efs :
  base_step tid e1 σ1 κ e2 σ2 efs →
  locs_expr e1 ⊆ dom σ1.(state_headers) →
  locs_state_in_headers σ1 →
  dom σ1.(state_headers) ⊆ dom σ2.(state_headers) ∧
  locs_expr e2 ⊆ dom σ2.(state_headers) ∧
  Forall (λ e, locs_expr e ⊆ dom σ2.(state_headers)) efs ∧
  locs_state_in_headers σ2.
Proof.
  intros Hbstep Hlocs Hσ.
  induction Hbstep; subst.
  (* State-preserving cases close fully; state-changing leave the full
     conjunction; in-between leave just [locs_expr e2 ⊆ …]. *)
  all: try (split_and!;
       [done | simpl in *; try set_solver | by constructor | done]).
  - (* App *)
    pose proof (locs_eval_app recs rec.1.2 v rec.2) as Hea.
    assert (locs_expr rec.2 ⊆ ⋃ ((λ r : recursive, locs_expr r.2) <$> recs)).
    { apply elem_of_subseteq. intros x Hx.
      apply elem_of_union_list. eexists. split; last exact Hx.
      apply list_elem_of_fmap. exists rec. split; first done.
      by eapply list_elem_of_lookup_2. }
    set_solver.
  - (* Let *) pose proof (locs_subst' x v1 e2). set_solver.
  - (* Unop *) rewrite (locs_eval_unop _ _ _ H). set_solver.
  - (* Binop *) rewrite (locs_eval_binop _ _ _ _ H). set_solver.
  - (* If *) destruct b; set_solver.
  - (* For *) case_decide; simpl; set_solver.
  - (* Alloc *) rewrite state_alloc_headers_dom. split_and!.
    + set_solver.
    + simpl. set_solver.
    + by constructor.
    + destruct Hσ as [Hlocals Hheap]. split.
      * eapply Forall_impl; [exact Hlocals|]. intros v Hv. set_solver.
      * intros l' v' Hlook.
        rewrite /state_alloc /= in Hlook.
        apply lookup_union_Some_raw in Hlook as [Hc|[_ Hold]].
        { apply chunk_lookup in Hc as (i & _ & _ & Hi).
          apply lookup_replicate in Hi as [-> _]. simpl. set_solver. }
        { specialize (Hheap _ _ Hold). set_solver. }
  - (* Block Mutable *) rewrite state_alloc_headers_dom. split_and!.
    + set_solver.
    + simpl. set_solver.
    + by constructor.
    + destruct Hσ as [Hlocals Hheap]. split.
      * eapply Forall_impl; [exact Hlocals|]. intros v Hv. set_solver.
      * intros l' v' Hlook.
        rewrite /state_alloc /= in Hlook.
        apply lookup_union_Some_raw in Hlook as [Hc|[_ Hold]].
        { apply chunk_lookup in Hc as (i & _ & _ & Hi).
          assert (locs_val v' ⊆ ⋃ (locs_val <$> vs)).
          { apply elem_of_subseteq. intros x Hx.
            apply elem_of_union_list. eexists. split; last exact Hx.
            apply list_elem_of_fmap. exists v'. split; first done.
            by eapply list_elem_of_lookup_2. }
          cbn in Hlocs.
          assert (⋃ (locs_val <$> vs) ⊆ dom (state_headers σ)).
          { rewrite -locs_of_vals.
            simpl in Hlocs. set_solver. }
          set_solver. }
        { specialize (Hheap _ _ Hold). set_solver. }
  - (* Block ImmutableNongenerative *) rewrite locs_of_vals in Hlocs. set_solver.
  - (* Block ImmutableGenerativeWeak *) rewrite locs_of_vals in Hlocs. set_solver.
  - (* Block ImmutableGenerativeStrong *) rewrite locs_of_vals in Hlocs. set_solver.
  - (* Match Mutable *)
    pose proof (locs_eval_match _ _ _ _ _ _ _ H0) as Hem.
    assert (locs_subj (SubjectLoc l) ⊆ dom (state_headers σ)) by (simpl; set_solver).
    set_solver.
  - (* Match Immutable *)
    pose proof (locs_eval_match _ _ _ _ _ _ _ H) as Hem.
    assert (locs_subj (SubjectBlock gen vs) ⊆ dom (state_headers σ)) by
      (simpl; set_solver).
    set_solver.
  - (* Get Field Mutable *)
    destruct Hσ as [_ Hheap]. specialize (Hheap _ _ H). set_solver.
  - (* Get Field Immutable *)
    assert (locs_val v ⊆ ⋃ (locs_val <$> vs)).
    { apply elem_of_subseteq. intros x Hx.
      apply elem_of_union_list. eexists. split; last exact Hx.
      apply list_elem_of_fmap. exists v. split; first done.
      by eapply list_elem_of_lookup_2. }
    set_solver.
  - (* Set Field *) rewrite state_set_location_headers. split_and!.
    + done.
    + simpl. set_solver.
    + by constructor.
    + destruct Hσ as [Hlocals Hheap]. split; [done|].
      intros l' v' Hlook. rewrite /state_set_location /= in Hlook.
      destruct (decide (l +ₗ fld = l')) as [<-|Hneq].
      * simplify_map_eq. set_solver.
      * rewrite lookup_insert_ne in Hlook; first by apply (Hheap _ _ Hlook).
        done.
  - (* Xchg *) rewrite state_set_location_headers. split_and!.
    + done.
    + destruct Hσ as [_ Hheap]. specialize (Hheap _ _ H). simpl. set_solver.
    + by constructor.
    + destruct Hσ as [Hlocals Hheap]. split; [done|].
      intros l' v' Hlook. rewrite /state_set_location /= in Hlook.
      destruct (decide (l +ₗ fld = l')) as [<-|Hneq].
      * simplify_map_eq. set_solver.
      * rewrite lookup_insert_ne in Hlook; first by apply (Hheap _ _ Hlook).
        done.
  - (* CAS success *) rewrite state_set_location_headers. split_and!.
    + done.
    + simpl. set_solver.
    + by constructor.
    + destruct Hσ as [Hlocals Hheap]. split; [done|].
      intros l' v' Hlook. rewrite /state_set_location /= in Hlook.
      destruct (decide (l +ₗ fld = l')) as [<-|Hneq].
      * simplify_map_eq. set_solver.
      * rewrite lookup_insert_ne in Hlook; first by apply (Hheap _ _ Hlook).
        done.
  - (* FAA *) rewrite state_set_location_headers. split_and!.
    + done.
    + simpl. set_solver.
    + by constructor.
    + destruct Hσ as [Hlocals Hheap]. split; [done|].
      intros l' v' Hlook. rewrite /state_set_location /= in Hlook.
      destruct (decide (l +ₗ fld = l')) as [<-|Hneq].
      * simplify_map_eq. simpl. set_solver.
      * rewrite lookup_insert_ne in Hlook; first by apply (Hheap _ _ Hlook).
        done.
  - (* Fork *) rewrite state_add_local_headers. split_and!.
    + done.
    + simpl. set_solver.
    + constructor; [|done]. cbn in Hlocs. set_solver.
    + destruct Hσ as [Hlocals Hheap]. split; [|done].
      apply Forall_app_2; [done|]. constructor; [|done].
      rewrite (locs_val_immediate _ H). set_solver.
  - (* GetLocal *)
    destruct Hσ as [Hlocals _].
    pose proof (Forall_lookup_1 _ _ _ _ Hlocals H) as Hv. set_solver.
  - (* SetLocal *) rewrite state_set_local_headers. split_and!.
    + done.
    + simpl. set_solver.
    + by constructor.
    + destruct Hσ as [Hlocals Hheap]. split; [|done].
      rewrite /state_set_local /=. apply Forall_insert; [done|].
      cbn in Hlocs. set_solver.
Qed.

Lemma silent_step_locs_in_headers es1 σ1 es2 σ2 :
  silent_step (es1, σ1) (es2, σ2) →
  Forall (locs_expr_in_headers σ1) es1 →
  locs_state_in_headers σ1 →
  Forall (locs_expr_in_headers σ2) es2 ∧
  locs_state_in_headers σ2.
Proof.
  intros [κ Hstep] Hes Hσ.
  destruct Hstep as (tid & e1 & e2 & σ2' & efs & Hpstep & Hlook & Heq).
  injection Heq as -> ->.
  inversion Hpstep as [K e1' e2' Heq1 Heq2 Hbstep]; subst e1 e2.
  pose proof (Forall_lookup_1 _ _ _ _ Hes Hlook) as He1.
  unfold locs_expr_in_headers in He1. rewrite locs_fill in He1.
  apply union_subseteq in He1 as [HKsub He1'].
  destruct (base_step_locs_in_headers _ _ _ _ _ _ _ Hbstep He1' Hσ)
    as (Hmono & He2' & Hefs & Hσ2).
  split; last done.
  apply Forall_app_2; last first.
  { eapply Forall_impl; [exact Hefs|]. intros e He.
    by rewrite /locs_expr_in_headers. }
  apply Forall_insert.
  { eapply Forall_impl; [exact Hes|]. intros e He.
    by rewrite /locs_expr_in_headers; etrans; [exact He|exact Hmono]. }
  rewrite /locs_expr_in_headers locs_fill. set_solver.
Qed.

Lemma rtc_silent_step_locs_in_headers es1 σ1 es2 σ2 :
  rtc silent_step (es1, σ1) (es2, σ2) →
  Forall (locs_expr_in_headers σ1) es1 →
  locs_state_in_headers σ1 →
  Forall (locs_expr_in_headers σ2) es2 ∧
  locs_state_in_headers σ2.
Proof.
  intros Hrtc.
  remember (es1, σ1) as c1 eqn:Hc1. remember (es2, σ2) as c2 eqn:Hc2.
  revert es1 σ1 es2 σ2 Hc1 Hc2.
  induction Hrtc as [c|c c' c'' Hstep _ IH]; intros es1 σ1 es2 σ2 -> Heq Hes Hσ.
  - injection Heq as -> ->. done.
  - destruct c' as [es' σ'].
    edestruct (silent_step_locs_in_headers _ _ _ _ Hstep Hes Hσ) as [Hes' Hσ'].
    by apply (IH _ _ _ _ eq_refl Heq).
Qed.

Lemma traced_steps_locs_in_headers es1 σ1 κ es2 σ2 :
  traced_steps (es1, σ1) κ (es2, σ2) →
  Forall (locs_expr_in_headers σ1) es1 →
  locs_state_in_headers σ1 →
  Forall (locs_expr_in_headers σ2) es2 ∧
  locs_state_in_headers σ2.
Proof.
  intros Htr Hes Hσ. eapply rtc_silent_step_locs_in_headers; [|done|done].
  by eapply traced_steps_rtc_silent_step.
Qed.

(** [decompose]'s redex never introduces new locations. *)
Lemma locs_decompose_fuel n e :
  locs_expr (decompose_fuel n e).2 ⊆ locs_expr e.
Proof.
  revert e. induction n as [|n IH]; intros e; simpl; first done.
  destruct (decompose_step e) as [[k e']|] eqn:Hd; last done.
  apply decompose_step_sound in Hd.
  destruct (decompose_fuel n e') as [K r] eqn:Hr; simpl.
  rewrite -Hd locs_filli.
  pose proof (IH e') as Hsub. rewrite Hr in Hsub. set_solver.
Qed.

Lemma locs_decompose e :
  locs_expr (decompose e).2 ⊆ locs_expr e.
Proof. apply locs_decompose_fuel. Qed.

Lemma locs_expr_in_headers_wf_header σ e :
  locs_expr_in_headers σ e → wf_header σ e.
Proof.
  rewrite /locs_expr_in_headers /wf_header.
  intros Hsub. pose proof (locs_decompose e) as Hd.
  destruct (decompose e).2 eqn:Hr; try done;
    repeat (match goal with
            | |- match ?x with _ => _ end => destruct x eqn:?; try done
            end);
    apply elem_of_dom; apply Hsub; apply Hd; simpl; set_solver.
Qed.

Lemma Forall_locs_expr_in_headers_wf_header σ es :
  Forall (locs_expr_in_headers σ) es →
  Forall (wf_header σ) es.
Proof.
  intros H. eapply Forall_impl; [exact H|].
  apply locs_expr_in_headers_wf_header.
Qed.

End locs_in_headers.
