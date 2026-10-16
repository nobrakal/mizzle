From iris.proofmode Require Import base proofmode.
From iris.bi.lib Require Import fixpoint_mono.
From iris.algebra Require Import view agree dfrac.
From iris.algebra.lib Require Import gmap_view.
From iris.base_logic Require Import gen_heap.
From iris.base_logic.lib Require Import own ghost_map.

Section go.
Context {Σ:gFunctors}.

Definition neg (P:iProp Σ) : iProp Σ :=
  P → False.

End go.

Section pointsto.

Context `{Countable L, hG : !gen_heapGS L V Σ}.

(** Pure helper: in a valid [gmap_view] over [agreeR (leibnizO V)], two
fragments at the same key both included in [c] must carry the same value. *)
Lemma gmap_view_agree_of_included
  (c : gmap_viewR L (agreeR (leibnizO V))) k dq1 dq2 v1 v2 :
  ✓ c →
  gmap_view_frag k dq1 (to_agree v1) ≼ c →
  gmap_view_frag k dq2 (to_agree v2) ≼ c →
  v1 = v2.
Proof.
  intros Hvc Hi1 Hi2.
  set (b1 := ({[k := (dq1, to_agree (v1 : leibnizO V))]} :
              gmapUR L (prodR dfracR (agreeR (leibnizO V))))).
  set (b2 := ({[k := (dq2, to_agree (v2 : leibnizO V))]} :
              gmapUR L (prodR dfracR (agreeR (leibnizO V))))).
  rewrite /gmap_view_frag -/b1 in Hi1.
  rewrite /gmap_view_frag -/b2 in Hi2.
  destruct Hi1 as [z1 Hz1].
  destruct Hi2 as [z2 Hz2].
  assert (Hb1 : b1 ≼ view_frag_proj c).
  { exists (view_frag_proj z1). by rewrite Hz1. }
  assert (Hb2 : b2 ≼ view_frag_proj c).
  { exists (view_frag_proj z2). by rewrite Hz2. }
  (* Extract a witness map satisfying gmap_view_rel from validity of [c]. *)
  rewrite cmra_valid_validN in Hvc.
  pose proof (Hvc inhabitant) as Hvc0. clear Hvc.
  rewrite iris.algebra.view.view_validN_eq /= in Hvc0.
  assert (Hrel : ∃ a : gmap L (agreeR (leibnizO V)),
          iris.algebra.lib.gmap_view.gmap_view_rel_raw
            L (agreeR (leibnizO V)) inhabitant a (view_frag_proj c)).
  { destruct (view_auth_proj c) as [[p x]|] eqn:Hauth;
    rewrite Hauth in Hvc0.
    - destruct Hvc0 as (_ & a & _ & Hr). by exists a.
    - destruct Hvc0 as (a & Hr). by exists a. }
  destruct Hrel as [a Hrel].
  rewrite lookup_included in Hb1.
  rewrite lookup_included in Hb2.
  specialize (Hb1 k). specialize (Hb2 k).
  subst b1 b2.
  rewrite lookup_singleton_eq in Hb1.
  rewrite lookup_singleton_eq in Hb2.
  destruct (view_frag_proj c !! k) as [[d ag]|] eqn:Hck; last first.
  { exfalso. rewrite Hck in Hb1.
    destruct Hb1 as [[[? ?]|] Heq]; inversion Heq. }
  specialize (Hrel k (d, ag) Hck) as (v_k & dq' & _ & [_ Hvk] & Hincl).
  simpl in *.
  rewrite Hck in Hb1, Hb2.
  apply cmra_included_includedN with (n := inhabitant) in Hb1.
  apply cmra_included_includedN with (n := inhabitant) in Hb2.
  apply Some_pair_includedN_r in Hb1.
  apply Some_pair_includedN_r in Hb2.
  apply (Some_pair_includedN_r _ d _ ag _) in Hincl.
  rewrite Some_includedN_total in Hb1.
  rewrite Some_includedN_total in Hb2.
  rewrite Some_includedN_total in Hincl.
  assert (Hag1 : to_agree v1 ≼{_} v_k)
    by (etrans; [apply Hb1|apply Hincl]).
  assert (Hag2 : to_agree v2 ≼{_} v_k)
    by (etrans; [apply Hb2|apply Hincl]).
  apply (agree_valid_includedN _ _ _ Hvk) in Hag1.
  apply (agree_valid_includedN _ _ _ Hvk) in Hag2.
  rewrite -Hag1 in Hag2.
  by apply (inj to_agree), leibniz_equiv in Hag2.
Qed.

Lemma pointsto_and_agree l dq1 dq2 v1 v2 :
  pointsto l dq1 v1 ∧ pointsto l dq2 v2 ⊢ ⌜v1 = v2⌝.
Proof.
  rewrite gen_heap.pointsto_unseal /gen_heap.pointsto_def.
  rewrite ghost_map.ghost_map_elem_unseal /ghost_map.ghost_map_elem_def.
  iIntros "H".
  iDestruct (own_and_total with "H") as (c) "[Hc [%H1 %H2]]".
  iDestruct (own_valid with "Hc") as %Hvc.
  iPureIntro. by eapply gmap_view_agree_of_included.
Qed.

End pointsto.

Section erase.
Context {Σ:gFunctor}.

(** [restrict s r] keeps only the entries of resource [r] whose ghost name
lies in [s], zeroing out everything else. *)
Definition restrict (s:gset gname) (r:iResUR Σ) : iResUR Σ :=
  λ i, filter (λ kv : gname * _, kv.1 ∈ s) (r i).

(** [co_restrict s r] keeps only entries whose ghost name is *not* in [s]. *)
Definition co_restrict (s:gset gname) (r:iResUR Σ) : iResUR Σ :=
  λ i, filter (λ kv : gname * _, kv.1 ∉ s) (r i).

Lemma restrict_ε s : restrict s ε ≡ ε.
Proof.
  intros i. rewrite /restrict.
  rewrite map_filter_empty //.
Qed.

Lemma restrict_op s (r1 r2 : iResUR Σ) :
  restrict s (r1 ⋅ r2) ≡ restrict s r1 ⋅ restrict s r2.
Proof.
  intros i k.
  rewrite discrete_fun_lookup_op /restrict !lookup_op !map_lookup_filter.
  rewrite discrete_fun_lookup_op lookup_op.
  destruct (decide (k ∈ s)) as [Hk|Hk];
    destruct (r1 i !! k) as [v1|] eqn:E1, (r2 i !! k) as [v2|] eqn:E2;
    rewrite ?E1 ?E2 /=;
    rewrite ?(option_guard_True _ Hk) ?(option_guard_False _ Hk) //.
  all: rewrite !option_guard_True //.
Qed.

Lemma restrict_included s (r : iResUR Σ) :
  restrict s r ≼ r.
Proof.
  apply discrete_fun_included_spec; intros i.
  apply lookup_included; intros k.
  rewrite /restrict map_lookup_filter.
  destruct (decide (k ∈ s)) as [Hk|Hk]; destruct (r i !! k) as [v|] eqn:E;
    rewrite ?E /=;
    rewrite ?(option_guard_True _ Hk) ?(option_guard_False _ Hk) //.
  all: rewrite ?option_guard_True //; apply option_included; auto.
Qed.

Global Instance restrict_ne s n : Proper (dist n ==> dist n) (restrict s).
Proof.
  intros a b Hab i k. specialize (Hab i k).
  rewrite /restrict !map_lookup_filter.
  destruct (a i !! k) as [v1|] eqn:Ea, (b i !! k) as [v2|] eqn:Eb;
    rewrite Ea Eb in Hab; rewrite ?Ea ?Eb /=.
  all: try (inversion Hab; done).
  destruct (decide (k ∈ s)) as [Hk|Hk];
    [rewrite !option_guard_True //; by f_equiv
    |rewrite !option_guard_False //].
Qed.

Global Instance restrict_proper s : Proper ((≡) ==> (≡)) (restrict s).
Proof.
  intros a b Hab i k. specialize (Hab i k).
  rewrite /restrict !map_lookup_filter.
  destruct (a i !! k) as [v1|] eqn:Ea, (b i !! k) as [v2|] eqn:Eb;
    rewrite Ea Eb in Hab; rewrite ?Ea ?Eb /=.
  all: try (inversion Hab; done).
  destruct (decide (k ∈ s)) as [Hk|Hk];
    [rewrite !option_guard_True //; by f_equiv
    |rewrite !option_guard_False //].
Qed.

Lemma restrict_idem s (r : iResUR Σ) :
  restrict s (restrict s r) ≡ restrict s r.
Proof.
  intros i k. rewrite /restrict !map_lookup_filter.
  destruct (r i !! k) as [v|] eqn:E; rewrite ?E /=; last done.
  cbn. destruct (decide (k ∈ s)) as [Hk|Hk].
  - rewrite !option_guard_True //. cbn. by rewrite !option_guard_True.
  - by rewrite !option_guard_False.
Qed.

Lemma restrict_monoN n s (a b : iResUR Σ) :
  a ≼{n} b → restrict s a ≼{n} restrict s b.
Proof.
  intros [c Hc]. exists (restrict s c).
  rewrite -restrict_op. by f_equiv.
Qed.

Lemma restrict_co_restrict s (r : iResUR Σ) :
  restrict s (co_restrict s r) ≡ ε.
Proof.
  intros i k. rewrite /restrict /co_restrict !map_lookup_filter.
  destruct (r i !! k) as [v|] eqn:E; rewrite ?E /=; last done.
  cbn. destruct (decide (k ∈ s)) as [Hk|Hk].
  - rewrite (option_guard_False (k ∉ s)) //. tauto.
  - rewrite (option_guard_True (k ∉ s)) //=.
    by rewrite option_guard_False.
Qed.

Lemma restrict_co_partition s (r : iResUR Σ) :
  restrict s r ⋅ co_restrict s r ≡ r.
Proof.
  intros i k. rewrite discrete_fun_lookup_op lookup_op.
  rewrite /restrict /co_restrict !map_lookup_filter.
  destruct (r i !! k) as [v|] eqn:E; rewrite ?E /=; last done.
  cbn. destruct (decide (k ∈ s)) as [Hk|Hk].
  - rewrite (option_guard_True (k ∈ s)) //.
    assert (Hk' : ¬ (k ∉ s)) by tauto.
    rewrite (option_guard_False _ Hk'). by rewrite right_id.
  - rewrite (option_guard_False (k ∈ s)) //.
    cbn. by rewrite option_guard_True.
Qed.

Lemma co_restrict_included s (r : iResUR Σ) :
  co_restrict s r ≼ r.
Proof.
  exists (restrict s r). rewrite (comm op). by rewrite restrict_co_partition.
Qed.


(** [sieve s P] holds at world [r] iff there is some sub-resource [r']
    of [r] with the same [s]-projection as [r] at which [P] holds.
    Intuitively, [sieve s P] is [P] holding on the [s]-part of [r]
    plus some outside-[s] padding. *)
Program Definition sieve_def (s : gset gname) (P : iProp Σ) : iProp Σ :=
  {| uPred_holds n r :=
    ∃ r', r' ≼{n} r ∧ restrict s r ≡{n}≡ restrict s r' ∧ uPred_holds P n r' |}.
Next Obligation.
  intros s P n1 n2 x1 x2 [r' (Hincl & Hres & HP)] Hxincl Hn.
  destruct Hxincl as [z Hz]. exists (r' ⋅ restrict s z). split_and!.
  - destruct Hincl as [w Hw]. exists (w ⋅ co_restrict s z).
    assert (Hw' : x1 ≡{n2}≡ r' ⋅ w) by by apply dist_le with n1.
    rewrite Hz Hw' -!assoc. f_equiv.
    rewrite (comm op (restrict s z)) -assoc. f_equiv.
    rewrite (comm op (co_restrict s z)). by rewrite restrict_co_partition.
  - rewrite Hz !restrict_op. apply cmra_op_ne'.
    + by apply (dist_le _ _ _ _ Hres).
    + by rewrite restrict_idem.
  - eapply uPred_mono; [exact HP|by exists (restrict s z)|exact Hn].
Qed.

Definition sieve_aux : seal (@sieve_def). Proof. by eexists. Qed.
Definition sieve := sieve_aux.(unseal).
Definition sieve_eq : @sieve = @sieve_def := sieve_aux.(seal_eq).

Lemma restrict_subset s s' (r : iResUR Σ) :
  s ⊆ s' → restrict s r ≼ restrict s' r.
Proof.
  intros Hsub.
  apply discrete_fun_included_spec; intros i.
  apply lookup_included; intros k.
  rewrite /restrict !map_lookup_filter.
  destruct (r i !! k) as [v|] eqn:E; rewrite ?E /=;
    last by apply option_included; left.
  destruct (decide (k ∈ s)) as [Hk|Hk];
    destruct (decide (k ∈ s')) as [Hk'|Hk'].
  - rewrite (option_guard_True (k ∈ s)) //.
    rewrite (option_guard_True (k ∈ s')) //.
  - exfalso. set_solver.
  - rewrite (option_guard_False (k ∈ s)) //. apply option_included; auto.
  - rewrite (option_guard_False (k ∈ s)) //. apply option_included; auto.
Qed.

Lemma sieve_holds s P n r :
  uPred_holds (sieve s P) n r ↔
  ∃ r', r' ≼{n} r ∧ restrict s r ≡{n}≡ restrict s r' ∧ uPred_holds P n r'.
Proof. by rewrite sieve_eq. Qed.

Lemma restrict_subset_eq s s' (r : iResUR Σ) :
  s ⊆ s' → restrict s r ≡ restrict s (restrict s' r).
Proof.
  intros Hsub i k. rewrite /restrict !map_lookup_filter.
  destruct (decide (k ∈ s)) as [Hk|Hk].
  - assert (Hk' : k ∈ s') by set_solver.
    destruct (r i !! k) as [v|] eqn:E; rewrite ?E /=; last done.
    rewrite !option_guard_True //=. by rewrite option_guard_True.
  - destruct (r i !! k) as [v|] eqn:E; rewrite ?E /=; last done.
    rewrite (option_guard_False (k ∈ s)) //.
    destruct (decide (k ∈ s')) as [Hk'|Hk'].
    + rewrite option_guard_True //=.
    + rewrite option_guard_False //.
Qed.

(** [P] implies [sieve s P]: take [r' := r]. *)
Lemma sieve_intro s P : P ⊢ sieve s P.
Proof.
  split=> n r Hv HP. apply sieve_holds.
  exists r. split_and!; [exists ε; by rewrite right_id|done|done].
Qed.

Lemma sieve_mono s P Q : (P ⊢ Q) → sieve s P ⊢ sieve s Q.
Proof.
  intros [HPQ]. split=> n r Hv /sieve_holds [r' [Hincl [Hres HP]]].
  apply sieve_holds. exists r'. split_and!; [done|done|].
  apply HPQ; [|done]. by eapply cmra_validN_includedN.
Qed.

Global Instance sieve_proper_entails s :
  Proper ((⊢) ==> (⊢)) (sieve s).
Proof. intros P Q. apply sieve_mono. Qed.

Global Instance sieve_proper_equiv s :
  Proper ((⊣⊢) ==> (⊣⊢)) (sieve s).
Proof.
  intros P Q HPQ. apply (anti_symm _);
    apply sieve_mono; rewrite HPQ //.
Qed.

(** A wider [s] makes the sieve stronger. *)
Lemma sieve_subset s s' P :
  s ⊆ s' → sieve s' P ⊢ sieve s P.
Proof.
  intros Hsub. split=> n r Hv /sieve_holds [r' [Hincl [Hres HP]]].
  apply sieve_holds. exists r'. split_and!; [done| |done].
  rewrite (restrict_subset_eq s s' r) // (restrict_subset_eq s s' r') //.
  by rewrite Hres.
Qed.

Lemma restrict_iRes_singleton `{!inG Σ A} γ (a:A) s :
  γ ∈ s → restrict s (own.iRes_singleton γ a) ≡ own.iRes_singleton γ a.
Proof.
  intros Hγ j. rewrite /own.iRes_singleton /restrict.
  destruct (decide (j = inG_id inG0)) as [->|Hne].
  - rewrite functions.discrete_fun_lookup_singleton.
    intros k. rewrite map_lookup_filter.
    destruct (decide (k = γ)) as [->|Hk]; last by rewrite lookup_singleton_ne.
    rewrite lookup_singleton_eq /=. by rewrite option_guard_True.
  - rewrite !functions.discrete_fun_lookup_singleton_ne //.
Qed.

Lemma restrict_iRes_singleton_out `{!inG Σ A} γ (a:A) s :
  γ ∉ s → restrict s (own.iRes_singleton γ a) ≡ ε.
Proof.
  intros Hγ j. rewrite /restrict /own.iRes_singleton.
  destruct (decide (j = inG_id inG0)) as [->|Hne].
  - rewrite functions.discrete_fun_lookup_singleton.
    intros k. rewrite map_lookup_filter.
    destruct (decide (k = γ)) as [->|Hk].
    + rewrite lookup_singleton_eq /=. rewrite option_guard_False //.
    + by rewrite lookup_singleton_ne.
  - rewrite functions.discrete_fun_lookup_singleton_ne //.
Qed.

Lemma iRes_singleton_validI `{!inG Σ A} γ (a:A) :
  ✓ a → ✓ (own.iRes_singleton γ a).
Proof.
  intros Hva. apply functions.discrete_fun_singleton_valid.
  apply singleton_valid. apply (cmra_morphism_valid own.inG_unfold).
  by rewrite cmra_transport_valid.
Qed.

(** Outside [s], the sieve carries no information about [γ]. *)
Lemma sieve_own_out `{!inG Σ A} γ (a:A) s :
  γ ∉ s → sieve s (own γ a) ⊢ True.
Proof. iIntros (?) "_". done. Qed.

(** [sieve] commutes with separating conjunction. *)
Lemma sieve_sep s P Q :
  sieve s P ∗ sieve s Q ⊢ sieve s (P ∗ Q).
Proof.
  rewrite /bi_entails /=. uPred.unseal. split=> n r Hv.
  rewrite /upred.uPred_sep_def /=. intros (r1 & r2 & Hr & HP & HQ).
  apply sieve_holds in HP as [r1' [Hincl1 [Hres1 HP]]].
  apply sieve_holds in HQ as [r2' [Hincl2 [Hres2 HQ]]].
  apply sieve_holds. exists (r1' ⋅ r2'). split_and!.
  - rewrite Hr. trans (r1 ⋅ r2'); [by apply cmra_monoN_r|by apply cmra_monoN_l].
  - rewrite Hr !restrict_op. by f_equiv.
  - rewrite /upred.uPred_sep_def /=. exists r1', r2'. done.
Qed.

(** [sieve] is transparent on names in [s] — without bupd. *)
Lemma sieve_own_in `{!inG Σ A} γ (a:A) s :
  γ ∈ s → sieve s (own γ a) ⊢ own γ a.
Proof.
  intros Hγ. rewrite own.own_eq /own.own_def.
  uPred.unseal. split=> n r Hv /sieve_holds [r' [Hincl [Hres Ha]]].
  unfold uPred_holds, upred.uPred_ownM_def in Ha |- *.
  apply cmra_includedN_trans with (restrict s r).
  - apply cmra_includedN_trans with (restrict s r').
    + rewrite -(restrict_iRes_singleton _ _ _ Hγ). by apply restrict_monoN.
    + by rewrite Hres.
  - apply cmra_included_includedN, restrict_included.
Qed.

(** Idempotence. *)
Lemma sieve_idemp s P :
  sieve s (sieve s P) ⊣⊢ sieve s P.
Proof.
  apply (anti_symm _); last apply sieve_intro.
  split=> n r Hv /sieve_holds [r1 [Hincl1 [Hres1 H1]]].
  apply sieve_holds in H1 as [r2 [Hincl2 [Hres2 HP]]].
  apply sieve_holds. exists r2. split_and!.
  - by etrans.
  - by etrans.
  - done.
Qed.

(** * Commutation with standard BI connectives and modalities *)

Lemma sieve_pure s φ : sieve s ⌜φ⌝ ⊣⊢ ⌜φ⌝.
Proof.
  apply (anti_symm _).
  - split=> n r Hv /sieve_holds [r' [_ [_ HP]]]. revert HP. uPred.unseal. done.
  - split=> n r Hv. uPred.unseal. intros HP.
    apply sieve_holds. exists r. split_and!; [|done|done].
    exists ε. by rewrite right_id.
Qed.

Lemma sieve_True s : sieve s True ⊣⊢ True.
Proof. apply (sieve_pure s True). Qed.

Lemma sieve_exist {A} s (Φ : A → iProp Σ) :
  sieve s (∃ x, Φ x) ⊣⊢ ∃ x, sieve s (Φ x).
Proof.
  apply (anti_symm _).
  - split=> n r Hv /sieve_holds [r' [Hincl [Hres HP]]].
    revert HP. uPred.unseal. intros [x HP].
    exists x. apply sieve_holds. by exists r'.
  - split=> n r Hv. uPred.unseal. intros [x Hx].
    apply sieve_holds in Hx as [r' [Hincl [Hres HP]]].
    apply sieve_holds. exists r'. split_and!; [done|done|].
    by exists x.
Qed.

Lemma sieve_or s P Q :
  sieve s (P ∨ Q) ⊣⊢ sieve s P ∨ sieve s Q.
Proof.
  apply (anti_symm _).
  - split=> n r Hv /sieve_holds [r' [Hincl [Hres HPQ]]].
    revert HPQ. uPred.unseal. intros [HP|HQ].
    + left. apply sieve_holds. by exists r'.
    + right. apply sieve_holds. by exists r'.
  - split=> n r Hv. uPred.unseal. intros [HP|HQ].
    + apply sieve_holds in HP as [r' [Hincl [Hres HP]]].
      apply sieve_holds. exists r'. split_and!; [done|done|by left].
    + apply sieve_holds in HQ as [r' [Hincl [Hres HQ]]].
      apply sieve_holds. exists r'. split_and!; [done|done|by right].
Qed.

Lemma sieve_forall {A} s (Φ : A → iProp Σ) :
  sieve s (∀ x, Φ x) ⊢ ∀ x, sieve s (Φ x).
Proof.
  split=> n r Hv /sieve_holds [r' [Hincl [Hres HP]]].
  revert HP. uPred.unseal. intros HP x.
  apply sieve_holds. exists r'. split_and!; [done|done|exact (HP x)].
Qed.

Lemma sieve_and s P Q :
  sieve s (P ∧ Q) ⊢ sieve s P ∧ sieve s Q.
Proof.
  split=> n r Hv /sieve_holds [r' [Hincl [Hres HPQ]]].
  revert HPQ. uPred.unseal. intros [HP HQ].
  split; apply sieve_holds; by exists r'.
Qed.

Lemma sieve_later s P : sieve s (▷ P) ⊢ ▷ sieve s P.
Proof.
  split=> n r Hv /sieve_holds [r' [Hincl [Hres HP]]].
  revert HP. uPred.unseal. intros HP.
  destruct n as [|m]; [done|].
  apply sieve_holds. unfold uPred_holds at 1 in HP. cbn in HP.
  exists r'. split_and!.
  - by apply cmra.cmra_includedN_S.
  - apply (dist_le _ _ _ _ Hres). lia.
  - done.
Qed.

(** [sieve] is right-distributive over separating conjunction in
    a strong way: any [P] can be pulled out of the sieve.  The
    witness uses [restrict_co_partition] to split the inclusion
    [r ≡ r' ⋅ z] into an [s]-part (which goes with the kept [P])
    and a co-[s]-part (which goes with the sieved remainder). *)
Lemma sieve_sep_inv s P Q :
  sieve s (P ∗ Q) ⊢ P ∗ sieve s Q.
Proof.
  split=> n r Hv /sieve_holds [r' [[z Hz] [_ HPQ]]].
  revert HPQ. uPred.unseal. intros (p & q & Hr' & HP & HQ).
  exists (p ⋅ restrict s z), (q ⋅ co_restrict s z). split_and!.
  - assert (Halg :
      (p ⋅ restrict s z) ⋅ (q ⋅ co_restrict s z) ≡ p ⋅ q ⋅ z).
    { rewrite -!assoc. f_equiv.
      rewrite (assoc op) (comm op (restrict s z) q) -(assoc op).
      f_equiv. apply restrict_co_partition. }
    etrans; [exact Hz|]. etrans; last by apply equiv_dist, symmetry, Halg.
    by f_equiv.
  - eapply uPred_mono; [exact HP|by exists (restrict s z)|done].
  - apply sieve_holds. exists q. split_and!.
    + by exists (co_restrict s z).
    + rewrite restrict_op. rewrite (_ : restrict s (co_restrict s z) ≡ ε);
        [by rewrite right_id|apply restrict_co_restrict].
    + done.
Qed.

(** Consequence: [sieve_sep] is actually an iff. *)
Lemma sieve_sep_iff s P Q :
  sieve s (P ∗ Q) ⊣⊢ sieve s P ∗ sieve s Q.
Proof.
  apply (anti_symm _); last apply sieve_sep.
  rewrite sieve_sep_inv.
  apply bi.sep_mono; [apply sieve_intro|done].
Qed.

Lemma sieve_except_0 s P : sieve s (◇ P) ⊢ ◇ sieve s P.
Proof.
  rewrite /bi_except_0. rewrite sieve_or. apply bi.or_mono; [|done].
  rewrite sieve_later. apply bi.later_mono. by rewrite sieve_pure.
Qed.

(** Distribution over the magic wand: derived from [sieve_sep] and
    [sieve_mono] via wand-introduction. *)
Lemma sieve_wand s P Q :
  sieve s (P -∗ Q) ⊢ sieve s P -∗ sieve s Q.
Proof.
  iIntros "H1 H2". iDestruct (sieve_sep with "[$H1 $H2]") as "H".
  iApply (sieve_mono with "H"). iIntros "[Hw HP]". by iApply "Hw".
Qed.

(** Distribution over [bupd]: pull the bupd out of the sieve.
    Witness: from inner bupd at [r'] with frame [w ⋅ yf] (where
    [r ≡ r' ⋅ w]), we get [x'] valid under [w ⋅ yf]; the new
    sieve-witness is [x' ⋅ co_restrict s w], dropping the
    [s]-part of [w] while keeping the outside. *)
Lemma sieve_bupd s P : sieve s (|==> P) ⊢ |==> sieve s P.
Proof.
  split=> n r Hv /sieve_holds [r' [Hincl [Hres HP]]].
  revert HP. uPred.unseal. intros HP.
  rewrite /uPred_holds /= in HP.
  intros k yf Hk Hvyf.
  destruct Hincl as [w Hw].
  assert (Hw' : r ≡{k}≡ r' ⋅ w) by by apply dist_le with n.
  destruct (HP k (w ⋅ yf)) as (x' & Hvx' & HPx');
    [done|by rewrite assoc -Hw'|].
  exists (x' ⋅ co_restrict s w). split.
  - apply cmra_validN_includedN with (x' ⋅ w ⋅ yf); [by rewrite -assoc|].
    rewrite -!assoc. apply cmra_monoN_l, cmra_monoN_r.
    exists (restrict s w). rewrite (comm op (co_restrict s w)).
    by rewrite restrict_co_partition.
  - apply sieve_holds. exists x'. split_and!.
    + exists (co_restrict s w). done.
    + rewrite restrict_op. rewrite (_ : restrict s (co_restrict s w) ≡ ε);
        [by rewrite right_id|apply restrict_co_restrict].
    + done.
Qed.

(** [<pers>] absorbs into [sieve] in one direction. *)
Lemma sieve_pers s P : <pers> (sieve s P) ⊢ sieve s (<pers> P).
Proof.
  split=> n r Hv. uPred.unseal. intros HP.
  apply sieve_holds in HP as [r' [Hincl [Hres HP]]].
  apply sieve_holds. exists r. split_and!.
  - exists ε. by rewrite right_id.
  - done.
  - unfold uPred_holds at 1. cbn.
    eapply uPred_mono; [exact HP|exact Hincl|done].
Qed.

End erase.

From iris.base_logic.lib Require Import fancy_updates wsat.

Section sieve_fupd.
Context {Σ : gFunctor} `{!invGS_gen HasNoLc Σ}.

(** Distribution over [fupd] (in the [HasNoLc] setting, where [fupd]
    expands to a wand into [|==> ◇ (...)]).  Proof: unseal [fupd],
    apply [sieve_wand], strengthen the premise via [sieve_intro],
    push [sieve] through [|==>] (via [sieve_bupd]) and [◇] (via
    [sieve_except_0]), and finally extract [wsat ∗ ownE E2] using
    [sieve_sep_inv]. *)
Lemma sieve_fupd s E1 E2 P :
  sieve s (|={E1,E2}=> P) ⊢ |={E1,E2}=> sieve s P.
Proof.
  rewrite fancy_updates.uPred_fupd_unseal /fancy_updates.uPred_fupd_def /=.
  iIntros "Hsv HwE".
  iAssert (sieve s (wsat ∗ ownE E1)) with "[HwE]" as "HwE'".
  { by iApply sieve_intro. }
  iDestruct (sieve_wand with "Hsv HwE'") as "Hsv".
  iDestruct (sieve_bupd with "Hsv") as ">Hsv".
  iDestruct (sieve_except_0 with "Hsv") as ">Hsv".
  iModIntro.
  iDestruct (sieve_sep_inv with "Hsv") as "[$ Hsv]".
  by iDestruct (sieve_sep_inv with "Hsv") as "[$ $]".
Qed.

End sieve_fupd.
