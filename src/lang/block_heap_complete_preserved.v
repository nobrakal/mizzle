From stdpp Require Import relations.
From iris.proofmode Require Import base proofmode.

From mizzle.lang Require Import instances.

From mizzle.logic Require Import interp wf_access completeness.

(** State invariant: every allocated block fills its full heap range.
    Operationally maintained by [state_alloc] (which puts a [chunk] of
    [hdr.size] values into [σ.heap]) and never broken thereafter, but
    not formalized at the [mirror_invs] level. *)
Definition block_heap_complete (σ : state) : Prop :=
  ∀ l hdr, σ.(state_headers) !! l = Some hdr →
  ∀ i, (i < header_size hdr)%nat →
       is_Some (σ.(state_heap) !! (l +ₗ Z.of_nat i)).

(** [block_heap_complete] is preserved by stepping. *)

Section block_heap_complete_preserved.

Lemma base_step_block_heap_complete tid e1 σ1 κ e2 σ2 efs :
  base_step tid e1 σ1 κ e2 σ2 efs →
  block_heap_complete σ1 →
  block_heap_complete σ2.
Proof.
  intros Hbstep Hbhc. induction Hbstep; subst; try done.
  - (* Alloc *) intros l' hdr' Hl' i Hi.
    rewrite /state_alloc /= in Hl' |- *.
    destruct (decide (l = l')) as [<-|Hne].
    + simplify_map_eq. simpl in Hi.
      apply lookup_union_is_Some. left.
      exists ValUnit. apply chunk_lookup. exists (Z.of_nat i).
      split; first lia. split; first by f_equal.
      rewrite Nat2Z.id lookup_replicate. split; [done|lia].
    + rewrite lookup_insert_ne // in Hl'.
      apply lookup_union_is_Some. right. by apply (Hbhc _ _ Hl').
  - (* Block Mutable *) intros l' hdr' Hl' i Hi.
    rewrite /state_alloc /= in Hl' |- *.
    destruct (decide (l = l')) as [<-|Hne].
    + simplify_map_eq. simpl in Hi.
      rewrite /of_vals length_fmap in Hi.
      apply lookup_union_is_Some. left.
      destruct (lookup_lt_is_Some_2 vs i Hi) as [v Hv].
      exists v. apply chunk_lookup. exists (Z.of_nat i).
      split; first lia. split; first by f_equal.
      rewrite Nat2Z.id //.
    + rewrite lookup_insert_ne // in Hl'.
      apply lookup_union_is_Some. right. by apply (Hbhc _ _ Hl').
  - (* Set Field *) intros l' hdr' Hl' i Hi.
    destruct (Hbhc _ _ Hl' _ Hi) as [w Hw].
    rewrite /state_set_location /=.
    destruct (decide (l +ₗ fld = l' +ₗ i)) as [<-|Hne].
    + simplify_map_eq. by eexists.
    + eexists. rewrite lookup_insert_ne; [exact Hw|done].
  - (* Xchg *) intros l' hdr' Hl' i Hi.
    destruct (Hbhc _ _ Hl' _ Hi) as [w' Hw'].
    rewrite /state_set_location /=.
    destruct (decide (l +ₗ fld = l' +ₗ i)) as [<-|Hne].
    + simplify_map_eq. by eexists.
    + eexists. rewrite lookup_insert_ne; [exact Hw'|done].
  - (* CAS success *) intros l' hdr' Hl' i Hi.
    destruct (Hbhc _ _ Hl' _ Hi) as [w Hw].
    rewrite /state_set_location /=.
    destruct (decide (l +ₗ fld = l' +ₗ i)) as [<-|Hne].
    + simplify_map_eq. by eexists.
    + eexists. rewrite lookup_insert_ne; [exact Hw|done].
  - (* FAA *) intros l' hdr' Hl' i Hi.
    destruct (Hbhc _ _ Hl' _ Hi) as [w Hw].
    rewrite /state_set_location /=.
    destruct (decide (l +ₗ fld = l' +ₗ i)) as [<-|Hne].
    + simplify_map_eq. by eexists.
    + eexists. rewrite lookup_insert_ne; [exact Hw|done].
Qed.

Lemma silent_step_block_heap_complete es1 σ1 es2 σ2 :
  silent_step (es1, σ1) (es2, σ2) →
  block_heap_complete σ1 →
  block_heap_complete σ2.
Proof.
  intros [κ Hstep] Hbhc.
  destruct Hstep as (tid & e1 & e2 & σ2' & efs & Hpstep & Hlook & Heq).
  injection Heq as -> ->.
  inversion Hpstep as [K e1' e2' Heq1 Heq2 Hbstep]; subst e1 e2.
  by eapply base_step_block_heap_complete.
Qed.

Lemma rtc_silent_step_block_heap_complete es1 σ1 es2 σ2 :
  rtc silent_step (es1, σ1) (es2, σ2) →
  block_heap_complete σ1 →
  block_heap_complete σ2.
Proof.
  intros Hrtc.
  remember (es1, σ1) as c1 eqn:Hc1. remember (es2, σ2) as c2 eqn:Hc2.
  revert es1 σ1 es2 σ2 Hc1 Hc2.
  induction Hrtc as [c|c c' c'' Hstep _ IH]; intros es1 σ1 es2 σ2 -> Heq Hbhc.
  - injection Heq as -> ->. done.
  - destruct c' as [es' σ'].
    pose proof (silent_step_block_heap_complete _ _ _ _ Hstep Hbhc) as Hbhc'.
    by apply (IH _ _ _ _ eq_refl Heq).
Qed.

Lemma traced_steps_block_heap_complete es1 σ1 κ es2 σ2 :
  traced_steps (es1, σ1) κ (es2, σ2) →
  block_heap_complete σ1 →
  block_heap_complete σ2.
Proof.
  intros Htr Hbhc. eapply rtc_silent_step_block_heap_complete; [|done].
  by eapply traced_steps_rtc_silent_step.
Qed.

End block_heap_complete_preserved.
