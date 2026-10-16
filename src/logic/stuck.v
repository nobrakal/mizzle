From iris.proofmode Require Import base proofmode.

From mizzle.lang Require Export semantics.

From mizzle.logic Require Import decompose interp goal wf_access.

(** A configuration is [Stuck] when some thread holds a non-value
    expression that is irreducible (ignoring out-of-bounds accesses). *)
Definition Stuck (es : list expr) (σ : state) : Prop :=
  ∃ p e, es !! p = Some e ∧ to_val e = None ∧ irreducible_no_oob p e σ.

(** A [base_irreducible] redex with no proper sub-redex is irreducible
    in any [fill K] context. *)
Lemma fill_irreducible tid K e σ :
  to_val e = None →
  sub_redexes_are_values e →
  base_irreducible tid e σ →
  irreducible tid (fill K e) σ.
Proof.
  intros Hnv Hsub Hirr κ e' σ' es Hstep.
  destruct Hstep as [K' e1' e2' Heq Heq' Hbase].
  edestruct (step_by_val tid K K') as [K'' Heq'']; eauto.
  subst K'. rewrite fill_app in Heq.
  apply (inj (fill K)) in Heq.
  assert (K'' = []) as HK''.
  { eapply Hsub; eauto using base_step_not_val. }
  subst K''. rewrite fill_nil in Heq. subst e1'.
  by eapply Hirr.
Qed.

(** [decompose_step e = None] when [e] is not a value implies that all
    immediate sub-redexes in evaluation position are already values. *)
Lemma decompose_step_none_sub_redexes e :
  decompose_step e = None →
  sub_redexes_are_values e.
Proof.
  intros Hd K e' Heq Hv.
  destruct K as [|k K _] using rev_ind; first done.
  exfalso.
  rewrite fill_snoc in Heq.
  assert (Hvf : to_val (fill K e') = None) by (apply to_val_fill; done).
  rewrite Heq (decompose_step_filli k _ Hvf) in Hd.
  discriminate.
Qed.

(** From [irreducible p (fill K r)], any base step on [r] lifts to a
    prim step on [fill K r], contradicting irreducibility. *)
Lemma irreducible_base_irred p K r σ :
  irreducible p (fill K r) σ →
  base_irreducible p r σ.
Proof.
  intros Hir κ r' σ' efs Hbase.
  eapply Hir.
  exact (base_step_fill_prim_step' K r r' eq_refl eq_refl Hbase).
Qed.

(** Decompose a non-value irreducible expression into an evaluation context
    [K] and a head redex [r] that is [base_irreducible] in [σ]. *)
Lemma irreducible_form p e σ :
  to_val e = None →
  irreducible p e σ →
  ∃ K r,
    e = fill K r ∧
    to_val r = None ∧
    sub_redexes_are_values r ∧
    base_irreducible p r σ.
Proof.
  intros Hv Hir.
  exists (decompose e).1, (decompose e).2.
  split; [|split; [|split]].
  - symmetry. exact (decompose_sound e).
  - exact (decompose_redex_not_val e Hv).
  - exact (decompose_step_none_sub_redexes _ (decompose_redex_no_step e)).
  - rewrite -(decompose_sound e) in Hir.
    exact (irreducible_base_irred p (decompose e).1 (decompose e).2 σ Hir).
Qed.

Section stuck.
Context `{seqlogGS Σ}.

Definition is_stuck p : iProp Σ :=
  ∀ es σ ts, interp es σ ts -∗
    ⌜∃ e, es !! p = Some e ∧ to_val e = None ∧ irreducible_no_oob p e σ⌝.

(** [If v _ _] with [v] not a boolean is stuck. *)
Lemma irreducible_if tid v e1 e2 σ :
  (match v with ValBool _ => False | _ => True end) →
  base_irreducible tid (If (Val v) e1 e2) σ.
Proof.
  intros Hbad κ e' σ' es Hstep. inversion Hstep; subst; done.
Qed.

Lemma sub_redexes_are_values_if v e1 e2 :
  sub_redexes_are_values (If (Val v) e1 e2).
Proof.
  apply sub_redexes_are_values_alt. intros [] e' Heq; simplify_eq/=; eauto.
Qed.

Lemma stuck_if p ks v e1 e2 :
  (match v with ValBool _ => False | _ => True end) →
  running p (fill ks (If (Val v) e1 e2)) -∗ is_stuck p.
Proof.
  iIntros (Hbad) "Hrun". rewrite /is_stuck.
  iIntros (es σ ts) "Hinterp".
  iDestruct (interp_running_exploit with "Hrun Hinterp") as %Hlk.
  iPureIntro. eexists. split_and!; [done|by apply fill_not_val|].
  apply irreducible_irreducible_no_oob.
  apply fill_irreducible; [done|apply sub_redexes_are_values_if|].
  by apply irreducible_if.
Qed.

(** [App (Val v) (Val w)] is stuck when [v] is not a [ValRecs]. *)
Lemma irreducible_call tid v w σ :
  (match v with ValRecs _ _ => False | _ => True end) →
  base_irreducible tid (App (Val v) (Val w)) σ.
Proof.
  intros Hbad κ e' σ' es Hstep. inversion Hstep; subst; done.
Qed.

Lemma sub_redexes_are_values_call v w :
  sub_redexes_are_values (App (Val v) (Val w)).
Proof.
  apply sub_redexes_are_values_alt. intros [] e' Heq; simplify_eq/=; eauto.
Qed.

Lemma stuck_call p ks v w :
  (match v with ValRecs _ _ => False | _ => True end) →
  running p (fill ks (App (Val v) (Val w))) -∗ is_stuck p.
Proof.
  iIntros (Hbad) "Hrun". rewrite /is_stuck.
  iIntros (es σ ts) "Hinterp".
  iDestruct (interp_running_exploit with "Hrun Hinterp") as %Hlk.
  iPureIntro. eexists. split_and!; [done|by apply fill_not_val|].
  apply irreducible_irreducible_no_oob.
  apply fill_irreducible; [done|apply sub_redexes_are_values_call|].
  by apply irreducible_call.
Qed.

(** [Unop op (Val v)] is stuck when [eval_unop op v = None]. *)
Lemma irreducible_unop tid op v σ :
  eval_unop op v = None →
  base_irreducible tid (Unop op (Val v)) σ.
Proof.
  intros Hnone κ e' σ' es Hstep. inversion Hstep; subst. congruence.
Qed.

Lemma sub_redexes_are_values_unop op v :
  sub_redexes_are_values (Unop op (Val v)).
Proof.
  apply sub_redexes_are_values_alt. intros [] e' Heq; simplify_eq/=; eauto.
Qed.

Lemma stuck_unop p ks op v :
  eval_unop op v = None →
  running p (fill ks (Unop op (Val v))) -∗ is_stuck p.
Proof.
  iIntros (Hnone) "Hrun". rewrite /is_stuck.
  iIntros (es σ ts) "Hinterp".
  iDestruct (interp_running_exploit with "Hrun Hinterp") as %Hlk.
  iPureIntro. eexists. split_and!; [done|by apply fill_not_val|].
  apply irreducible_irreducible_no_oob.
  apply fill_irreducible; [done|apply sub_redexes_are_values_unop|].
  by apply irreducible_unop.
Qed.

(** [Binop op (Val v1) (Val v2)] is stuck when [eval_binop op v1 v2 = None]. *)
Lemma irreducible_binop tid op v1 v2 σ :
  eval_binop op v1 v2 = None →
  base_irreducible tid (Binop op (Val v1) (Val v2)) σ.
Proof.
  intros Hnone κ e' σ' es Hstep. inversion Hstep; subst. congruence.
Qed.

Lemma sub_redexes_are_values_binop op v1 v2 :
  sub_redexes_are_values (Binop op (Val v1) (Val v2)).
Proof.
  apply sub_redexes_are_values_alt. intros [] e' Heq; simplify_eq/=; eauto.
Qed.

Lemma stuck_binop p ks op v1 v2 :
  eval_binop op v1 v2 = None →
  running p (fill ks (Binop op (Val v1) (Val v2))) -∗ is_stuck p.
Proof.
  iIntros (Hnone) "Hrun". rewrite /is_stuck.
  iIntros (es σ ts) "Hinterp".
  iDestruct (interp_running_exploit with "Hrun Hinterp") as %Hlk.
  iPureIntro. eexists. split_and!; [done|by apply fill_not_val|].
  apply irreducible_irreducible_no_oob.
  apply fill_irreducible; [done|apply sub_redexes_are_values_binop|].
  by apply irreducible_binop.
Qed.

(** [For (Val v1) (Val v2) e] is stuck when [v1] or [v2] is not a [ValInt]. *)
Lemma irreducible_for tid v1 v2 e σ :
  (match v1, v2 with ValInt _, ValInt _ => False | _, _ => True end) →
  base_irreducible tid (For (Val v1) (Val v2) e) σ.
Proof.
  intros Hbad κ e' σ' es Hstep. inversion Hstep; subst; done.
Qed.

Lemma sub_redexes_are_values_for v1 v2 e :
  sub_redexes_are_values (For (Val v1) (Val v2) e).
Proof.
  apply sub_redexes_are_values_alt. intros [] e' Heq; simplify_eq/=; eauto.
Qed.

Lemma stuck_for p ks v1 v2 e :
  (match v1, v2 with ValInt _, ValInt _ => False | _, _ => True end) →
  running p (fill ks (For (Val v1) (Val v2) e)) -∗ is_stuck p.
Proof.
  iIntros (Hbad) "Hrun". rewrite /is_stuck.
  iIntros (es σ ts) "Hinterp".
  iDestruct (interp_running_exploit with "Hrun Hinterp") as %Hlk.
  iPureIntro. eexists. split_and!; [done|by apply fill_not_val|].
  apply irreducible_irreducible_no_oob.
  apply fill_irreducible; [done|apply sub_redexes_are_values_for|].
  by apply irreducible_for.
Qed.

(** [Match (Val v) x e0 brs] stuck when [v] is neither a location nor a block. *)
Lemma irreducible_match tid v x e0 brs σ :
  (match v with ValLoc _ => False | ValBlock _ _ _ => False | _ => True end) →
  base_irreducible tid (Match (Val v) x e0 brs) σ.
Proof.
  intros Hbad κ e' σ' es Hstep. inversion Hstep; subst; done.
Qed.

Lemma sub_redexes_are_values_match v x e0 brs :
  sub_redexes_are_values (Match (Val v) x e0 brs).
Proof.
  apply sub_redexes_are_values_alt. intros [] e' Heq; simplify_eq/=; eauto.
Qed.

Lemma stuck_match p ks v x e0 brs :
  (match v with ValLoc _ => False | ValBlock _ _ _ => False | _ => True end) →
  running p (fill ks (Match (Val v) x e0 brs)) -∗ is_stuck p.
Proof.
  iIntros (Hbad) "Hrun". rewrite /is_stuck.
  iIntros (es σ ts) "Hinterp".
  iDestruct (interp_running_exploit with "Hrun Hinterp") as %Hlk.
  iPureIntro. eexists. split_and!; [done|by apply fill_not_val|].
  apply irreducible_irreducible_no_oob.
  apply fill_irreducible; [done|apply sub_redexes_are_values_match|].
  by apply irreducible_match.
Qed.

(** [GetTag (Val v)] stuck when [v] is not a location or block. *)
Lemma irreducible_gettag tid v σ :
  (match v with ValLoc _ => False | ValBlock _ _ _ => False | _ => True end) →
  base_irreducible tid (GetTag (Val v)) σ.
Proof.
  intros Hbad κ e' σ' es Hstep. inversion Hstep; subst; done.
Qed.

Lemma sub_redexes_are_values_gettag v :
  sub_redexes_are_values (GetTag (Val v)).
Proof.
  apply sub_redexes_are_values_alt. intros [] e' Heq; simplify_eq/=; eauto.
Qed.

Lemma stuck_gettag p ks v :
  (match v with ValLoc _ => False | ValBlock _ _ _ => False | _ => True end) →
  running p (fill ks (GetTag (Val v))) -∗ is_stuck p.
Proof.
  iIntros (Hbad) "Hrun". rewrite /is_stuck.
  iIntros (es σ ts) "Hinterp".
  iDestruct (interp_running_exploit with "Hrun Hinterp") as %Hlk.
  iPureIntro. eexists. split_and!; [done|by apply fill_not_val|].
  apply irreducible_irreducible_no_oob.
  apply fill_irreducible; [done|apply sub_redexes_are_values_gettag|].
  by apply irreducible_gettag.
Qed.

(** [GetSize (Val v)] stuck in the same conditions as [GetTag]. *)
Lemma irreducible_getsize tid v σ :
  (match v with ValLoc _ => False | ValBlock _ _ _ => False | _ => True end) →
  base_irreducible tid (GetSize (Val v)) σ.
Proof.
  intros Hbad κ e' σ' es Hstep. inversion Hstep; subst; done.
Qed.

Lemma sub_redexes_are_values_getsize v :
  sub_redexes_are_values (GetSize (Val v)).
Proof.
  apply sub_redexes_are_values_alt. intros [] e' Heq; simplify_eq/=; eauto.
Qed.

Lemma stuck_getsize p ks v :
  (match v with ValLoc _ => False | ValBlock _ _ _ => False | _ => True end) →
  running p (fill ks (GetSize (Val v))) -∗ is_stuck p.
Proof.
  iIntros (Hbad) "Hrun". rewrite /is_stuck.
  iIntros (es σ ts) "Hinterp".
  iDestruct (interp_running_exploit with "Hrun Hinterp") as %Hlk.
  iPureIntro. eexists. split_and!; [done|by apply fill_not_val|].
  apply irreducible_irreducible_no_oob.
  apply fill_irreducible; [done|apply sub_redexes_are_values_getsize|].
  by apply irreducible_getsize.
Qed.

(** [GetField atm (Val v1) (Val v2)] stuck when types do not match any load form.
    Note: [ValNat n = ValInt (Z.of_nat n)], so both load forms use [ValInt]. *)
Lemma irreducible_get_field tid v1 v2 σ (atm : atomicity) :
  (match v1 with
   | ValLoc _ => match v2 with ValInt _ => False | _ => True end
   | ValBlock _ _ _ => match v2 with ValInt _ => False | _ => True end
   | _ => True end) →
  base_irreducible tid (GetField atm (Val v1) (Val v2)) σ.
Proof.
  intros Hbad κ e' σ' es Hstep. inversion Hstep; subst; done.
Qed.

Lemma sub_redexes_are_values_get_field v1 v2 (atm : atomicity) :
  sub_redexes_are_values (GetField atm (Val v1) (Val v2)).
Proof.
  apply sub_redexes_are_values_alt. intros [] e' Heq; simplify_eq/=; eauto.
Qed.

Lemma stuck_get_field p ks v1 v2 (atm : atomicity) :
  (match v1 with
   | ValLoc _ => match v2 with ValInt _ => False | _ => True end
   | ValBlock _ _ _ => match v2 with ValInt _ => False | _ => True end
   | _ => True end) →
  running p (fill ks (GetField atm (Val v1) (Val v2))) -∗ is_stuck p.
Proof.
  iIntros (Hbad) "Hrun". rewrite /is_stuck.
  iIntros (es σ ts) "Hinterp".
  iDestruct (interp_running_exploit with "Hrun Hinterp") as %Hlk.
  iPureIntro. eexists. split_and!; [done|by apply fill_not_val|].
  apply irreducible_irreducible_no_oob.
  apply fill_irreducible; [done|apply sub_redexes_are_values_get_field|].
  by apply irreducible_get_field.
Qed.

(** [SetField atm (Val v1) (Val v2) (Val v3)] stuck when types do not match. *)
Lemma irreducible_set_field tid v1 v2 v3 σ (atm : atomicity) :
  (match v1, v2 with ValLoc _, ValInt _ => False | _, _ => True end) →
  base_irreducible tid (SetField atm (Val v1) (Val v2) (Val v3)) σ.
Proof.
  intros Hbad κ e' σ' es Hstep. inversion Hstep; subst; done.
Qed.

Lemma sub_redexes_are_values_set_field v1 v2 v3 (atm : atomicity) :
  sub_redexes_are_values (SetField atm (Val v1) (Val v2) (Val v3)).
Proof.
  apply sub_redexes_are_values_alt. intros [] e' Heq; simplify_eq/=; eauto.
Qed.

Lemma stuck_set_field p ks v1 v2 v3 (atm : atomicity) :
  (match v1, v2 with ValLoc _, ValInt _ => False | _, _ => True end) →
  running p (fill ks (SetField atm (Val v1) (Val v2) (Val v3))) -∗ is_stuck p.
Proof.
  iIntros (Hbad) "Hrun". rewrite /is_stuck.
  iIntros (es σ ts) "Hinterp".
  iDestruct (interp_running_exploit with "Hrun Hinterp") as %Hlk.
  iPureIntro. eexists. split_and!; [done|by apply fill_not_val|].
  apply irreducible_irreducible_no_oob.
  apply fill_irreducible; [done|apply sub_redexes_are_values_set_field|].
  by apply irreducible_set_field.
Qed.

(** [Xchg (Val v1) (Val v2)] stuck when [v1] is not a valid loc/field tuple. *)
Lemma irreducible_xchg tid v1 v2 σ :
  (match v1 with ValTuple [ValLoc _; ValInt _] => False | _ => True end) →
  base_irreducible tid (Xchg (Val v1) (Val v2)) σ.
Proof.
  intros Hbad κ e' σ' es Hstep. inversion Hstep; subst; done.
Qed.

Lemma sub_redexes_are_values_xchg v1 v2 :
  sub_redexes_are_values (Xchg (Val v1) (Val v2)).
Proof.
  apply sub_redexes_are_values_alt. intros [] e' Heq; simplify_eq/=; eauto.
Qed.

Lemma stuck_xchg p ks v1 v2 :
  (match v1 with ValTuple [ValLoc _; ValInt _] => False | _ => True end) →
  running p (fill ks (Xchg (Val v1) (Val v2))) -∗ is_stuck p.
Proof.
  iIntros (Hbad) "Hrun". rewrite /is_stuck.
  iIntros (es σ ts) "Hinterp".
  iDestruct (interp_running_exploit with "Hrun Hinterp") as %Hlk.
  iPureIntro. eexists. split_and!; [done|by apply fill_not_val|].
  apply irreducible_irreducible_no_oob.
  apply fill_irreducible; [done|apply sub_redexes_are_values_xchg|].
  by apply irreducible_xchg.
Qed.

(** [CAS (Val v0) (Val v1) (Val v2)] stuck when [v0] is not a valid loc/field tuple. *)
Lemma irreducible_cas tid v0 v1 v2 σ :
  (match v0 with ValTuple [ValLoc _; ValInt _] => False | _ => True end) →
  base_irreducible tid (CAS (Val v0) (Val v1) (Val v2)) σ.
Proof.
  intros Hbad κ e' σ' es Hstep. inversion Hstep; subst; done.
Qed.

Lemma sub_redexes_are_values_cas v0 v1 v2 :
  sub_redexes_are_values (CAS (Val v0) (Val v1) (Val v2)).
Proof.
  apply sub_redexes_are_values_alt. intros [] e' Heq; simplify_eq/=; eauto.
Qed.

Lemma stuck_cas p ks v0 v1 v2 :
  (match v0 with ValTuple [ValLoc _; ValInt _] => False | _ => True end) →
  running p (fill ks (CAS (Val v0) (Val v1) (Val v2))) -∗ is_stuck p.
Proof.
  iIntros (Hbad) "Hrun". rewrite /is_stuck.
  iIntros (es σ ts) "Hinterp".
  iDestruct (interp_running_exploit with "Hrun Hinterp") as %Hlk.
  iPureIntro. eexists. split_and!; [done|by apply fill_not_val|].
  apply irreducible_irreducible_no_oob.
  apply fill_irreducible; [done|apply sub_redexes_are_values_cas|].
  by apply irreducible_cas.
Qed.

(** [FAA (Val v1) (Val v2)] stuck when types do not match [ValTuple [ValLoc; ValInt]] × [ValInt]. *)
Lemma irreducible_faa tid v1 v2 σ :
  (match v1 with
   | ValTuple [ValLoc _; ValInt _] =>
       match v2 with ValInt _ => False | _ => True end
   | _ => True end) →
  base_irreducible tid (FAA (Val v1) (Val v2)) σ.
Proof.
  intros Hbad κ e' σ' es Hstep. inversion Hstep; subst; done.
Qed.

Lemma sub_redexes_are_values_faa v1 v2 :
  sub_redexes_are_values (FAA (Val v1) (Val v2)).
Proof.
  apply sub_redexes_are_values_alt. intros [] e' Heq; simplify_eq/=; eauto.
Qed.

Lemma stuck_faa p ks v1 v2 :
  (match v1 with
   | ValTuple [ValLoc _; ValInt _] =>
       match v2 with ValInt _ => False | _ => True end
   | _ => True end) →
  running p (fill ks (FAA (Val v1) (Val v2))) -∗ is_stuck p.
Proof.
  iIntros (Hbad) "Hrun". rewrite /is_stuck.
  iIntros (es σ ts) "Hinterp".
  iDestruct (interp_running_exploit with "Hrun Hinterp") as %Hlk.
  iPureIntro. eexists. split_and!; [done|by apply fill_not_val|].
  apply irreducible_irreducible_no_oob.
  apply fill_irreducible; [done|apply sub_redexes_are_values_faa|].
  by apply irreducible_faa.
Qed.

(** [App (Val (ValRecs i recs)) (Val v)] with index [i] missing is stuck. *)
Lemma irreducible_app_bad tid i recs v σ :
  recs !! i = None →
  base_irreducible tid (App (Val (ValRecs i recs)) (Val v)) σ.
Proof.
  intros Hi κ e' σ' es Hstep. inversion Hstep; subst. congruence.
Qed.

Lemma stuck_app p ks i recs v :
  recs !! i = None →
  running p (fill ks (App (Val (ValRecs i recs)) (Val v))) -∗ is_stuck p.
Proof.
  iIntros (Hi) "Hrun". rewrite /is_stuck.
  iIntros (es σ ts) "Hinterp".
  iDestruct (interp_running_exploit with "Hrun Hinterp") as %Hlk.
  iPureIntro. eexists. split_and!; [done|by apply fill_not_val|].
  apply irreducible_irreducible_no_oob.
  apply fill_irreducible; [done|apply sub_redexes_are_values_call|].
  by apply irreducible_app_bad.
Qed.

(** [Alloc (Val v1) (Val v2)] with wrong argument types is stuck. *)
Lemma sub_redexes_are_values_alloc v1 v2 :
  sub_redexes_are_values (Alloc (Val v1) (Val v2)).
Proof.
  apply sub_redexes_are_values_alt. intros [] e' Heq; simplify_eq/=; eauto.
Qed.

Lemma irreducible_alloc tid v1 v2 σ :
  (match v1 with
   | ValInt _ => match v2 with ValInt _ => False | _ => True end
   | _ => True end) →
  base_irreducible tid (Alloc (Val v1) (Val v2)) σ.
Proof.
  intros Hbad κ e' σ' es Hstep. inversion Hstep; subst; done.
Qed.

Lemma stuck_alloc p ks v1 v2 :
  (match v1 with
   | ValInt _ => match v2 with ValInt _ => False | _ => True end
   | _ => True end) →
  running p (fill ks (Alloc (Val v1) (Val v2))) -∗ is_stuck p.
Proof.
  iIntros (Hbad) "Hrun". rewrite /is_stuck.
  iIntros (es σ ts) "Hinterp".
  iDestruct (interp_running_exploit with "Hrun Hinterp") as %Hlk.
  iPureIntro. eexists. split_and!; [done|by apply fill_not_val|].
  apply irreducible_irreducible_no_oob.
  apply fill_irreducible; [done|apply sub_redexes_are_values_alloc|].
  by apply irreducible_alloc.
Qed.

(** [Alloc (Val (ValInt z)) (Val (ValInt n))] with negative tag or size. *)
Lemma irreducible_alloc_neg tid z n σ :
  (z < 0 ∨ n < 0)%Z →
  base_irreducible tid (Alloc (Val (ValInt z)) (Val (ValInt n))) σ.
Proof.
  intros Hneg κ e' σ' es Hstep. inversion Hstep; simplify_eq; lia.
Qed.

Lemma stuck_alloc_neg p ks z n :
  (z < 0 ∨ n < 0)%Z →
  running p (fill ks (Alloc (Val (ValInt z)) (Val (ValInt n)))) -∗ is_stuck p.
Proof.
  iIntros (Hneg) "Hrun". rewrite /is_stuck.
  iIntros (es σ ts) "Hinterp".
  iDestruct (interp_running_exploit with "Hrun Hinterp") as %Hlk.
  iPureIntro. eexists. split_and!; [done|by apply fill_not_val|].
  apply irreducible_irreducible_no_oob.
  apply fill_irreducible; [done|apply sub_redexes_are_values_alloc|].
  by apply irreducible_alloc_neg.
Qed.

(** [Block Mutable tag []] is stuck (empty mutable block). *)
Lemma sub_redexes_are_values_block_mutable_empty tag :
  sub_redexes_are_values (Block Mutable tag []).
Proof.
  apply sub_redexes_are_values_alt. intros [] e' Heq; simplify_eq/=; eauto.
  destruct es; done.
Qed.

Lemma irreducible_block_mutable_empty tid tag σ :
  base_irreducible tid (Block Mutable tag []) σ.
Proof.
  intros κ e' σ' es Hstep. inversion Hstep; subst; simpl in *; lia.
Qed.

Lemma stuck_block_mutable_empty p ks tag :
  running p (fill ks (Block Mutable tag [])) -∗ is_stuck p.
Proof.
  iIntros "Hrun". rewrite /is_stuck.
  iIntros (es σ ts) "Hinterp".
  iDestruct (interp_running_exploit with "Hrun Hinterp") as %Hlk.
  iPureIntro. eexists. split_and!; [done|by apply fill_not_val|].
  apply irreducible_irreducible_no_oob.
  apply fill_irreducible; [done|apply sub_redexes_are_values_block_mutable_empty|].
  by apply irreducible_block_mutable_empty.
Qed.

(** [Match (Val (ValBlock gen tag vs)) x e brs] with no matching branch. *)
Lemma irreducible_match_immutable_no_branch tid gen tag vs x e brs σ :
  eval_match tag (length vs) (SubjectBlock gen vs) x e brs = None →
  base_irreducible tid (Match (Val (ValBlock gen tag vs)) x e brs) σ.
Proof.
  intros Hem κ e' σ' es Hstep. inversion Hstep; subst; congruence.
Qed.

Lemma stuck_match_immutable_no_branch p ks gen tag vs x e brs :
  eval_match tag (length vs) (SubjectBlock gen vs) x e brs = None →
  running p (fill ks (Match (Val (ValBlock gen tag vs)) x e brs)) -∗ is_stuck p.
Proof.
  iIntros (Hem) "Hrun". rewrite /is_stuck.
  iIntros (es σ ts) "Hinterp".
  iDestruct (interp_running_exploit with "Hrun Hinterp") as %Hlk.
  iPureIntro. eexists. split_and!; [done|by apply fill_not_val|].
  apply irreducible_irreducible_no_oob.
  apply fill_irreducible; [done|apply sub_redexes_are_values_match|].
  by apply irreducible_match_immutable_no_branch.
Qed.

(** [GetTag (Val (ValBlock gen tag []))] is stuck (empty block has no tag). *)
Lemma irreducible_gettag_immutable_empty tid gen tag σ :
  base_irreducible tid (GetTag (Val (ValBlock gen tag []))) σ.
Proof.
  intros κ e' σ' es Hstep. inversion Hstep; subst; simpl in *; lia.
Qed.

Lemma stuck_gettag_immutable_empty p ks gen tag :
  running p (fill ks (GetTag (Val (ValBlock gen tag [])))) -∗ is_stuck p.
Proof.
  iIntros "Hrun". rewrite /is_stuck.
  iIntros (es σ ts) "Hinterp".
  iDestruct (interp_running_exploit with "Hrun Hinterp") as %Hlk.
  iPureIntro. eexists. split_and!; [done|by apply fill_not_val|].
  apply irreducible_irreducible_no_oob.
  apply fill_irreducible; [done|apply sub_redexes_are_values_gettag|].
  by apply irreducible_gettag_immutable_empty.
Qed.

(** [GetSize (Val (ValBlock gen tag []))] is stuck (empty block has no size). *)
Lemma irreducible_getsize_immutable_empty tid gen tag σ :
  base_irreducible tid (GetSize (Val (ValBlock gen tag []))) σ.
Proof.
  intros κ e' σ' es Hstep. inversion Hstep; subst; simpl in *; lia.
Qed.

Lemma stuck_getsize_immutable_empty p ks gen tag :
  running p (fill ks (GetSize (Val (ValBlock gen tag [])))) -∗ is_stuck p.
Proof.
  iIntros "Hrun". rewrite /is_stuck.
  iIntros (es σ ts) "Hinterp".
  iDestruct (interp_running_exploit with "Hrun Hinterp") as %Hlk.
  iPureIntro. eexists. split_and!; [done|by apply fill_not_val|].
  apply irreducible_irreducible_no_oob.
  apply fill_irreducible; [done|apply sub_redexes_are_values_getsize|].
  by apply irreducible_getsize_immutable_empty.
Qed.

(** [GetField atm (Val (ValBlock gen tag vs)) (Val (ValInt fld))] out of range. *)
Lemma irreducible_get_field_block tid gen tag vs fld σ (atm : atomicity) :
  (∀ n : nat, Z.of_nat n = fld → vs !! n = None) →
  base_irreducible tid (GetField atm (Val (ValBlock gen tag vs)) (Val (ValInt fld))) σ.
Proof.
  intros Hrange κ e' σ' es Hstep. inversion Hstep; simplify_eq;
    specialize (Hrange _ eq_refl); congruence.
Qed.

Lemma stuck_get_field_block p ks gen tag vs fld (atm : atomicity) :
  (∀ n : nat, Z.of_nat n = fld → vs !! n = None) →
  running p (fill ks (GetField atm (Val (ValBlock gen tag vs)) (Val (ValInt fld)))) -∗ is_stuck p.
Proof.
  iIntros (Hrange) "Hrun". rewrite /is_stuck.
  iIntros (es σ ts) "Hinterp".
  iDestruct (interp_running_exploit with "Hrun Hinterp") as %Hlk.
  iPureIntro. eexists. split_and!; [done|by apply fill_not_val|].
  apply irreducible_irreducible_no_oob.
  apply fill_irreducible; [done|apply sub_redexes_are_values_get_field|].
  by apply irreducible_get_field_block.
Qed.

(** [Var x] is stuck (an open term cannot step). *)
Lemma sub_redexes_are_values_var x :
  sub_redexes_are_values (Var x).
Proof.
  apply sub_redexes_are_values_alt. intros [] e' Heq; simplify_eq/=; eauto.
Qed.

Lemma irreducible_var tid x σ :
  base_irreducible tid (Var x) σ.
Proof.
  intros κ e' σ' es Hstep. inversion Hstep.
Qed.

Lemma stuck_var p ks x :
  running p (fill ks (Var x)) -∗ is_stuck p.
Proof.
  iIntros "Hrun". rewrite /is_stuck.
  iIntros (es σ ts) "Hinterp".
  iDestruct (interp_running_exploit with "Hrun Hinterp") as %Hlk.
  iPureIntro. eexists. split_and!; [done|by apply fill_not_val|].
  apply irreducible_irreducible_no_oob.
  apply fill_irreducible; [done|apply sub_redexes_are_values_var|].
  by apply irreducible_var.
Qed.

(** [FAA] on a heap cell that holds a non-integer is stuck. *)
Lemma irreducible_faa_not_int tid l fld n v σ :
  state_heap σ !! (l +ₗ fld) = Some v →
  (∀ m : Z, v ≠ ValInt m) →
  base_irreducible tid (FAA (Val (ValTuple [ValLoc l; ValInt fld])) (Val (ValInt n))) σ.
Proof.
  intros Hcell Hni κ e' σ' es Hstep. inversion Hstep; simplify_eq;
    exact (Hni _ eq_refl).
Qed.

Lemma stuck_faa_not_int p ks l fld n v :
  (∀ m : Z, v ≠ ValInt m) →
  (l +ₗ fld) ↦ v -∗
  running p (fill ks (FAA (Val (ValTuple [ValLoc l; ValInt fld])) (Val (ValInt n)))) -∗
  is_stuck p.
Proof.
  iIntros (Hni) "Hcell Hrun". rewrite /is_stuck.
  iIntros (es σ ts) "Hinterp".
  iDestruct (interp_running_exploit with "Hrun Hinterp") as %Hlk.
  iDestruct (interp_get_field with "Hinterp Hcell") as %Hcell.
  iPureIntro. eexists. split_and!; [done|by apply fill_not_val|].
  apply irreducible_irreducible_no_oob.
  apply fill_irreducible; [done|apply sub_redexes_are_values_faa|].
  by eapply irreducible_faa_not_int.
Qed.

(** [Match] on a location whose header yields no matching branch.  Needs the
    persistent header to pin [σ]'s header for [l]. *)
Lemma irreducible_match_mutable_no_branch tid l hdr x e brs σ :
  state_headers σ !! l = Some hdr →
  eval_match (header_tag hdr) (header_size hdr) (SubjectLoc l) x e brs = None →
  base_irreducible tid (Match (Val (ValLoc l)) x e brs) σ.
Proof.
  intros Hlk Hem κ e' σ' es Hstep. inversion Hstep; simplify_eq; congruence.
Qed.

Lemma stuck_match_mutable_no_branch p ks l hdr x e brs :
  eval_match (header_tag hdr) (header_size hdr) (SubjectLoc l) x e brs = None →
  l ↦ₕ□ hdr -∗
  running p (fill ks (Match (Val (ValLoc l)) x e brs)) -∗ is_stuck p.
Proof.
  iIntros (Hem) "#Hhdr Hrun". rewrite /is_stuck.
  iIntros (es σ ts) "Hinterp".
  iDestruct (interp_running_exploit with "Hrun Hinterp") as %Hrun.
  iDestruct (interp_get_field_header with "Hinterp Hhdr") as %Hlk.
  iPureIntro. eexists. split_and!; [done|by apply fill_not_val|].
  apply irreducible_irreducible_no_oob.
  apply fill_irreducible; [done|apply sub_redexes_are_values_match|].
  by eapply irreducible_match_mutable_no_branch.
Qed.

(** Out-of-bounds field accesses: the persistent header pins the block size,
    so [wf_access] is unsatisfiable and the redex is [irreducible_no_oob]. *)
Lemma stuck_get_field_oob p ks l fld hdr (atm : atomicity) :
  ¬ (0 ≤ fld < header_size hdr)%Z →
  l ↦ₕ□ hdr -∗
  running p (fill ks (GetField atm (Val (ValLoc l)) (Val (ValInt fld)))) -∗ is_stuck p.
Proof.
  iIntros (Hoob) "#Hhdr Hrun". rewrite /is_stuck.
  iIntros (es σ ts) "Hinterp".
  iDestruct (interp_running_exploit with "Hrun Hinterp") as %Hrun.
  iDestruct (interp_get_field_header with "Hinterp Hhdr") as %Hlk.
  iPureIntro. eexists. split_and!; [done|by apply fill_not_val|].
  intros κ e' σ' efs Hstep Hwa.
  apply wf_access_fill in Hwa; try done.
  unfold wf_access in Hwa; simpl in Hwa.
  destruct Hwa as (hdr' & Hlk' & Hbd). rewrite Hlk in Hlk'. by simplify_eq.
Qed.

Lemma stuck_set_field_oob p ks l fld v hdr (atm : atomicity) :
  ¬ (0 ≤ fld < header_size hdr)%Z →
  l ↦ₕ□ hdr -∗
  running p (fill ks (SetField atm (Val (ValLoc l)) (Val (ValInt fld)) (Val v))) -∗ is_stuck p.
Proof.
  iIntros (Hoob) "#Hhdr Hrun". rewrite /is_stuck.
  iIntros (es σ ts) "Hinterp".
  iDestruct (interp_running_exploit with "Hrun Hinterp") as %Hrun.
  iDestruct (interp_get_field_header with "Hinterp Hhdr") as %Hlk.
  iPureIntro. eexists. split_and!; [done|by apply fill_not_val|].
  intros κ e' σ' efs Hstep Hwa.
  apply wf_access_fill in Hwa; try done.
  unfold wf_access in Hwa; simpl in Hwa.
  destruct Hwa as (hdr' & Hlk' & Hbd). rewrite Hlk in Hlk'. by simplify_eq.
Qed.

Lemma stuck_xchg_oob p ks l fld v hdr :
  ¬ (0 ≤ fld < header_size hdr)%Z →
  l ↦ₕ□ hdr -∗
  running p (fill ks (Xchg (Val (ValTuple [ValLoc l; ValInt fld])) (Val v))) -∗ is_stuck p.
Proof.
  iIntros (Hoob) "#Hhdr Hrun". rewrite /is_stuck.
  iIntros (es σ ts) "Hinterp".
  iDestruct (interp_running_exploit with "Hrun Hinterp") as %Hrun.
  iDestruct (interp_get_field_header with "Hinterp Hhdr") as %Hlk.
  iPureIntro. eexists. split_and!; [done|by apply fill_not_val|].
  intros κ e' σ' efs Hstep Hwa.
  apply wf_access_fill in Hwa; try done.
  unfold wf_access in Hwa; simpl in Hwa.
  destruct Hwa as (hdr' & Hlk' & Hbd). rewrite Hlk in Hlk'. by simplify_eq.
Qed.

Lemma stuck_cas_oob p ks l fld v1 v2 hdr :
  ¬ (0 ≤ fld < header_size hdr)%Z →
  l ↦ₕ□ hdr -∗
  running p (fill ks (CAS (Val (ValTuple [ValLoc l; ValInt fld])) (Val v1) (Val v2))) -∗ is_stuck p.
Proof.
  iIntros (Hoob) "#Hhdr Hrun". rewrite /is_stuck.
  iIntros (es σ ts) "Hinterp".
  iDestruct (interp_running_exploit with "Hrun Hinterp") as %Hrun.
  iDestruct (interp_get_field_header with "Hinterp Hhdr") as %Hlk.
  iPureIntro. eexists. split_and!; [done|by apply fill_not_val|].
  intros κ e' σ' efs Hstep Hwa.
  apply wf_access_fill in Hwa; try done.
  unfold wf_access in Hwa; simpl in Hwa.
  destruct Hwa as (hdr' & Hlk' & Hbd). rewrite Hlk in Hlk'. by simplify_eq.
Qed.

Lemma stuck_faa_oob p ks l fld n hdr :
  ¬ (0 ≤ fld < header_size hdr)%Z →
  l ↦ₕ□ hdr -∗
  running p (fill ks (FAA (Val (ValTuple [ValLoc l; ValInt fld])) (Val (ValInt n)))) -∗ is_stuck p.
Proof.
  iIntros (Hoob) "#Hhdr Hrun". rewrite /is_stuck.
  iIntros (es σ ts) "Hinterp".
  iDestruct (interp_running_exploit with "Hrun Hinterp") as %Hrun.
  iDestruct (interp_get_field_header with "Hinterp Hhdr") as %Hlk.
  iPureIntro. eexists. split_and!; [done|by apply fill_not_val|].
  intros κ e' σ' efs Hstep Hwa.
  apply wf_access_fill in Hwa; try done.
  unfold wf_access in Hwa; simpl in Hwa.
  destruct Hwa as (hdr' & Hlk' & Hbd). rewrite Hlk in Hlk'. by simplify_eq.
Qed.

Definition is_stuck' : iProp Σ := ∃ p, is_stuck p.

End stuck.
