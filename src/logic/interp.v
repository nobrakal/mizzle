From iris.proofmode Require Import base proofmode.
From iris.algebra Require Import gset auth.
From iris.base_logic.lib Require Export fancy_updates.
From iris.base_logic.lib Require Export gen_heap ghost_map.
From iris.base_logic.lib Require Export saved_prop.
From iris.base_logic.lib Require Export own.
From iris.base_logic.lib Require Export ghost_var.

From mizzle.logic Require Import negation.

From mizzle.lang Require Export semantics.

Class seqlogGS (Σ:gFunctors) :=
  SeqlogGS {
      iinvgs : invGS_gen HasLc Σ;
      iheap : gen_heapGS location val Σ;
      iheaders : gen_heapGS location header Σ;
      γsplit : gname;
      isplit : ghost_mapG Σ nat expr;
      γlocals : gname;
      ilocals : ghost_mapG Σ nat val;
      isprop : savedPropG Σ;
      γinit : gname;
      ilocset : inG Σ (authR (gset_disjUR location));
      γlocset : gname;
      itrace : ghost_mapG Σ unit (list observation);
      γtrace : gname;
    }.

#[global] Existing Instance iinvgs.
#[global] Existing Instance iheap.
#[global] Existing Instance iheaders.
#[global] Existing Instance isplit.
#[global] Existing Instance ilocals.
#[global] Existing Instance isprop.
#[global] Existing Instance ilocset.
#[global] Existing Instance itrace.

Notation "l ↦ₕ dq hdr" := (pointsto (V:=header) l dq hdr)
  (at level 20, dq custom dfrac at level 1, format "l  ↦ₕ dq  hdr") : bi_scope.

Notation "γ ↪PROP dq P" := (saved_prop_own γ dq P)
  (at level 20, dq custom dfrac at level 1,
   format "γ  ↪PROP dq  P").

Definition loc_auth `{seqlogGS Σ} (S : gset location) : iProp Σ :=
  own γlocset (● GSet S).

Definition loc_tok `{seqlogGS Σ} (T : gset location) : iProp Σ :=
  own γlocset (◯ GSet T).

Definition loc_tok1 `{seqlogGS Σ} (l : location) : iProp Σ :=
  loc_tok {[l]}.

(** Bundled user-facing heap pointsto: a normal [pointsto] together
    with the exclusive auth fragment [loc_tok1 l]. Owning [l ↦ v]
    therefore witnesses both "the heap value at [l] is [v]" and "I
    own the live-location token for [l]", giving same-location
    exclusion via [loc_tok1_exclusive] without going through
    [gen_heap.pointsto_ne]. *)

Definition mz_pointsto `{seqlogGS Σ} (l : location) (dq : dfrac) (v : val) : iProp Σ :=
  pointsto (V:=val) l dq v ∗ loc_tok1 l.

Notation "l ↦ dq v" := (mz_pointsto l dq v)
  (at level 20, dq custom dfrac at level 1, format "l  ↦ dq  v") : bi_scope.

#[global] Instance mz_pointsto_timeless `{seqlogGS Σ} l dq v :
  Timeless (l ↦{dq} v).
Proof. rewrite /mz_pointsto. apply _. Qed.

(** Blocked heap pointsto: a whole block at [l] described by its contents
    [vs = [x1; …; xn]]. Bundles the (persistent) header — whose size is
    exactly [length vs], pinning the block bounds — with the contiguous
    cells. The block's tag is existentially packed. *)
Definition mz_block `{seqlogGS Σ} (l : location) (dq : dfrac) (vs : list val) : iProp Σ :=
  ∃ tag, l ↦ₕ□ Header tag (length vs) ∗
         [∗ list] i ↦ v ∈ vs, (l +ₗ Z.of_nat i) ↦{dq} v.

Notation "l ↦∗ dq vs" := (mz_block l dq vs)
  (at level 20, dq custom dfrac at level 1, format "l  ↦∗ dq  vs") : bi_scope.

#[global] Instance mz_block_timeless `{seqlogGS Σ} l dq vs :
  Timeless (l ↦∗{dq} vs).
Proof. rewrite /mz_block. apply _. Qed.

Section interp.

Context `{seqlogGS Σ}.

Definition remaining Q : iProp Σ :=
  ∃ P, γinit ↪PROP□ P ∗ (Q -∗ P).

Lemma update_remaining Q Q' :
  (Q' -∗ Q) -∗
  remaining Q -∗
  remaining Q'.
Proof.
  iIntros "HQQ' (%Qcur & Hcur & HQQcur)".
  iExists Qcur. iFrame "Hcur".
  iIntros "HQ'". iApply "HQQcur". by iApply "HQQ'".
Qed.

(** Trace ghost. There is one global trace, so the map is held at the single
    key [()] mapping to the observations [Emit] has recorded so far (= [ts]).
    The trace is ghost: it lives only here and in [prim_step]'s observation
    list, and no program can read it back. *)
Definition trace_interp (ts : list observation) : iProp Σ :=
  ghost_map_auth γtrace 1 {[() := ts]}.

Definition interp (es:list expr) σ (ts : list observation) : iProp Σ :=
    ⌜length es = length σ.(state_locals)⌝ ∗
    gen_heap_interp σ.(state_heap) ∗
    gen_heap_interp σ.(state_headers) ∗
    ghost_map_auth γsplit 1 (map_seq 0 es) ∗
    ghost_map_auth γlocals 1 (map_seq 0 σ.(state_locals)) ∗
    loc_auth (dom σ.(state_heap) ∪ dom σ.(state_headers)) ∗
    trace_interp ts.

Definition running (i:nat) (e:expr) :=
  ghost_map_elem γsplit i (DfracOwn 1) e.

Definition local (i:nat) (v:val) :=
  ghost_map_elem γlocals i (DfracOwn 1) v.

(** The trace so far is exactly [tr]. *)
Definition trace_model (tr : list observation) :=
  ghost_map_elem γtrace () (DfracOwn 1) tr.

(** Canonical initial state: empty heap/headers and a single local [v0]. *)
Definition initial_state (v0 : val) : state :=
  {| state_headers := ∅; state_heap := ∅;
     state_locals := [v0] |}.

Lemma loc_tok_op T1 T2 :
  T1 ## T2 →
  loc_tok T1 ∗ loc_tok T2 ⊣⊢ loc_tok (T1 ∪ T2).
Proof.
  intros Hdisj. rewrite /loc_tok -own_op -auth_frag_op gset_disj_union //.
Qed.

Lemma loc_tok_disjoint T1 T2 :
  loc_tok T1 -∗ loc_tok T2 -∗ ⌜T1 ## T2⌝.
Proof.
  iIntros "H1 H2".
  iDestruct (own_valid_2 with "H1 H2") as %Hv.
  rewrite -auth_frag_op auth_frag_valid gset_disj_valid_op in Hv. done.
Qed.

Lemma loc_tok1_exclusive l :
  loc_tok1 l -∗ loc_tok1 l -∗ False.
Proof.
  iIntros "H1 H2".
  iDestruct (loc_tok_disjoint with "H1 H2") as %Hd.
  iPureIntro. set_solver.
Qed.

Lemma loc_tok_subset S T :
  loc_auth S -∗ loc_tok T -∗ ⌜T ⊆ S⌝.
Proof.
  iIntros "Hauth Hfrag".
  iDestruct (own_valid_2 with "Hauth Hfrag") as %Hv.
  apply auth_both_valid_discrete in Hv as [Hincl _].
  apply gset_disj_included in Hincl. done.
Qed.

Lemma loc_tok1_in S l :
  loc_auth S -∗ loc_tok1 l -∗ ⌜l ∈ S⌝.
Proof.
  iIntros "Hauth Htok".
  iDestruct (loc_tok_subset with "Hauth Htok") as %Hsub.
  iPureIntro. set_solver.
Qed.

Lemma loc_alloc S T :
  T ## S →
  loc_auth S ==∗ loc_auth (S ∪ T) ∗ loc_tok T.
Proof.
  iIntros (Hdisj) "Hauth".
  iMod (own_update _ _ (● GSet (T ∪ S) ⋅ ◯ GSet T) with "Hauth") as "[Hauth Hfrag]".
  { apply auth_update_alloc. by apply gset_disj_alloc_empty_local_update. }
  rewrite (comm_L (∪) T S). iModIntro. iFrame.
Qed.

Lemma loc_alloc1 S l :
  l ∉ S →
  loc_auth S ==∗ loc_auth (S ∪ {[l]}) ∗ loc_tok1 l.
Proof. intros Hnotin. apply loc_alloc. set_solver. Qed.

Lemma mz_pointsto_split l dq v :
  l ↦{dq} v ⊣⊢ pointsto (V:=val) l dq v ∗ loc_tok1 l.
Proof. done. Qed.

(** Same-location exclusion via the bundled [loc_tok1]: two bundled
    pointstos at the same address contradict because [loc_tok1] is
    exclusive in [gset_disj]. *)
Lemma mz_pointsto_exclusive l dq1 v1 dq2 v2 :
  l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ False.
Proof.
  iIntros "[_ Ht1] [_ Ht2]".
  iApply (loc_tok1_exclusive with "Ht1 Ht2").
Qed.

(** Different-location lemma: [↦{dq1} v1] and [↦{dq2} v2] at two
    different locations have disjoint [loc_tok] fragments. [[card]] *)
Lemma mz_pointsto_ne l1 dq1 v1 l2 dq2 v2 :
  l1 ↦{dq1} v1 -∗ l2 ↦{dq2} v2 -∗ ⌜l1 ≠ l2⌝.
Proof.
  iIntros "[_ Ht1] [_ Ht2]".
  iDestruct (loc_tok_disjoint with "Ht1 Ht2") as %Hdisj.
  iPureIntro. intros ->. set_solver.
Qed.

(** ∧-form value agreement: when both bundled pointstos hold under the
    same resources (intuitionistic conjunction), the underlying values
    must agree. Unlike the ∗-form (which is subsumed by
    [mz_pointsto_exclusive]), this is a genuine agreement statement
    because ∧ does not imply spatial separation. *)
Lemma mz_pointsto_and_agree l dq1 dq2 v1 v2 :
  l ↦{dq1} v1 ∧ l ↦{dq2} v2 ⊢ ⌜v1 = v2⌝.
Proof.
  iIntros "H".
  iAssert (pointsto (V:=val) l dq1 v1 ∧ pointsto (V:=val) l dq2 v2)%I
    with "[H]" as "Hp".
  { iSplit.
    - iDestruct (bi.and_elim_l with "H") as "H".
      rewrite mz_pointsto_split. iDestruct "H" as "[$ _]".
    - iDestruct (bi.and_elim_r with "H") as "H".
      rewrite mz_pointsto_split. iDestruct "H" as "[$ _]". }
  iApply (pointsto_and_agree with "Hp").
Qed.

Lemma interp_running_exploit p e es σ ts:
  running p e -∗ interp es σ ts -∗ ⌜es !! p = Some e⌝.
Proof.
  rewrite /interp /running.
  iIntros "Hrun (_ & _ & _ & Hauth & _ & _)".
  iDestruct (ghost_map_lookup with "Hauth Hrun") as %Hlook.
  apply lookup_map_seq_Some in Hlook as [_ Hlook].
  rewrite Nat.sub_0_r in Hlook.
  done.
Qed.

Lemma interp_local_exploit p v es σ ts:
  local p v -∗ interp es σ ts -∗ ⌜σ.(state_locals) !! p = Some v⌝.
Proof.
  rewrite /interp /local.
  iIntros "Hloc (_ & _ & _ & _ & Hauth & _)".
  iDestruct (ghost_map_lookup with "Hauth Hloc") as %Hlook.
  apply lookup_map_seq_Some in Hlook as [_ Hlook].
  rewrite Nat.sub_0_r in Hlook.
  done.
Qed.

Lemma interp_run e' p e es σ ts :
  running p e -∗ interp es σ ts ==∗ running p e' ∗ interp (<[p:=e']> es) σ ts.
Proof.
  rewrite /interp /running.
  iIntros "Hrun (%Hlen & $ & $ & Hauth & $ & $)".
  iDestruct (ghost_map_lookup with "Hauth Hrun") as %Hlook.
  apply lookup_map_seq_Some in Hlook as [_ Hlook].
  rewrite Nat.sub_0_r in Hlook.
  apply lookup_lt_Some in Hlook.
  iMod (ghost_map_update e' with "Hauth Hrun") as "[Hauth $]".
  iModIntro. iSplit.
  { iPureIntro. by rewrite length_insert. }
  rewrite -insert_map_seq_0 //.
Qed.

Lemma interp_set_local p v w es σ ts :
  local p v -∗ interp es σ ts ==∗ local p w ∗ interp es (state_set_local p w σ) ts.
Proof.
  rewrite /interp /local.
  iIntros "Hloc (%Hlen & $ & $ & $ & Hauth & Hls)".
  iDestruct (ghost_map_lookup with "Hauth Hloc") as %Hlook.
  apply lookup_map_seq_Some in Hlook as [_ Hlook].
  rewrite Nat.sub_0_r in Hlook.
  pose proof (lookup_lt_Some _ _ _ Hlook) as Hlt.
  iMod (ghost_map_update w with "Hauth Hloc") as "[Hauth $]".
  iModIntro. iSplit.
  { iPureIntro. simpl. rewrite /state_set_local /state_update_locals /=.
    by rewrite length_insert. }
  simpl. rewrite /state_set_local /state_update_locals /=.
  rewrite -insert_map_seq_0 //. iFrame.
Qed.

(** Record an [Emit]: append the observation [v] to the trace. The state is
    untouched, so [interp es σ] is preserved. *)
Lemma interp_emit v tr es σ ts :
  interp es σ ts -∗ trace_model tr ==∗
    interp es σ (ts ++ [v]) ∗ trace_model (tr ++ [v]).
Proof.
  iIntros "(%Hlen & Hheap & Hhdrs & Hsplit & Hloc & Hls & Hpauth) Htr".
  iDestruct (ghost_map_lookup with "Hpauth Htr") as %Hlook.
  rewrite lookup_singleton_Some in Hlook. destruct Hlook as [_ <-].
  iMod (ghost_map_update (ts ++ [v]) with "Hpauth Htr") as "[Hpauth Htr]".
  iModIntro. iFrame "Htr".
  rewrite /interp /trace_interp.
  iFrame "Hheap Hhdrs Hsplit Hloc Hls".
  iSplitR; first (iPureIntro; exact Hlen).
  rewrite insert_singleton. iFrame "Hpauth".
Qed.

(** Read-off: the held fragment [trace_model tr] pins [tr] to the trace [ts].
    Applied at adequacy to the final [interp es σ κ], this lets the user
    deduce facts about the constructed trace [κ]. *)
Lemma interp_trace es σ ts tr :
  interp es σ ts -∗ trace_model tr -∗ ⌜tr = ts⌝.
Proof.
  iIntros "(_ & _ & _ & _ & _ & _ & Hpauth) Htr".
  iDestruct (ghost_map_lookup with "Hpauth Htr") as %Hlook.
  iPureIntro. rewrite lookup_singleton_Some in Hlook. by destruct Hlook as [_ ->].
Qed.

Lemma interp_fork v p e e' ef es σ ts :
  running p e -∗ interp es σ ts ==∗
  running p e' ∗ running (length es) ef ∗ local (length es) v ∗
  interp (<[p:=e']> es ++ [ef]) (state_add_local v σ) ts.
Proof.
  rewrite /interp /running /local.
  iIntros "Hrun (%Hlen & $ & $ & Hsplit & Hloc & $)".
  iDestruct (ghost_map_lookup with "Hsplit Hrun") as %Hlook.
  apply lookup_map_seq_Some in Hlook as [_ Hlook].
  rewrite Nat.sub_0_r in Hlook.
  pose proof (lookup_lt_Some _ _ _ Hlook) as Hlt.
  iMod (ghost_map_update e' with "Hsplit Hrun") as "[Hsplit $]".
  iMod (ghost_map_insert (length es) ef with "Hsplit") as "[Hsplit $]".
  { apply lookup_insert_None. split; last lia.
    apply lookup_map_seq_None. right. lia. }
  iMod (ghost_map_insert (length σ.(state_locals)) v with "Hloc") as "[Hloc Hv]".
  { apply lookup_map_seq_None. right. lia. }
  iModIntro.
  rewrite -Hlen. iFrame "Hv".
  iSplit.
  { iPureIntro. simpl. rewrite /state_add_local /state_update_locals /=.
    simpl_length/=. lia. }
  rewrite map_seq_snoc length_insert Nat.add_0_l.
  rewrite -insert_map_seq_0; last lia.
  iFrame "Hsplit".
  simpl. rewrite /state_add_local /state_update_locals /=.
  rewrite map_seq_snoc Nat.add_0_l.
  iFrame.
  rewrite Hlen. iFrame.
Qed.

Lemma chunk_to_seq_pointsto l (vs : list val) :
  ([∗ map] l' ↦ v ∈ chunk l vs, pointsto (V:=val) l' (DfracOwn 1) v) ⊣⊢
  [∗ list] i ↦ v ∈ vs, pointsto (V:=val) (l +ₗ Z.of_nat i) (DfracOwn 1) v.
Proof.
  revert l. induction vs as [|v vs IH]; intros l; simpl.
  { by rewrite big_sepM_empty. }
  rewrite big_opM_insert; last first.
  { destruct (chunk (l +ₗ 1) vs !! l) eqn:Hl; last done.
    exfalso. apply chunk_lookup in Hl as (j & ? & Hj & _).
    rewrite location_add_assoc in Hj.
    rewrite -{1}(location_add_0 l) in Hj.
    apply (inj (location_add l)) in Hj. lia. }
  rewrite location_add_0.
  rewrite IH.
  apply bi.sep_proper; first done.
  apply big_sepL_proper => i v' _.
  rewrite Nat2Z.inj_succ -Z.add_1_l location_add_assoc //.
Qed.

(** [loc_tok] of the empty set is affinely discardable since [◯ GSet ∅]
    is the unit of the auth fragment CMRA. *)
Lemma loc_tok_empty : loc_tok ∅ ⊢ emp.
Proof. iIntros "_". done. Qed.

(** Distribute [loc_tok (dom (chunk l vs))] across the cells. *)
Lemma loc_tok_chunk_distribute l (vs : list val) :
  loc_tok (dom (chunk l vs)) ⊢
  [∗ list] i ↦ _ ∈ vs, loc_tok1 (l +ₗ Z.of_nat i).
Proof.
  revert l. induction vs as [|v vs IH]; intros l; simpl.
  { rewrite dom_empty_L. iApply loc_tok_empty. }
  rewrite dom_insert_L.
  assert (Hdisj : {[l]} ## dom (chunk (l +ₗ 1) vs)).
  { apply disjoint_singleton_l. intros [w Hw]%elem_of_dom.
    apply chunk_lookup in Hw as (j & Hj0 & Heq & _).
    rewrite location_add_assoc in Heq.
    rewrite -{1}(location_add_0 l) in Heq.
    apply (inj (location_add l)) in Heq. lia. }
  rewrite -loc_tok_op //.
  iIntros "[Hl Hrest]". rewrite /loc_tok1 location_add_0. iFrame "Hl".
  iPoseProof (IH with "Hrest") as "Hcells".
  iApply (big_sepL_mono with "Hcells").
  iIntros (i v' _) "H".
  rewrite Nat2Z.inj_succ -Z.add_1_l location_add_assoc //.
Qed.

Lemma interp_block_mutable l es σ ts tag (vs:list val) :
  σ.(state_headers) !! l = None →
  σ.(state_heap) !! l = None →
  (∀ i, i < length vs → σ.(state_heap) !! (l +ₗ i) = None) →
  (∀ i, i < length vs → σ.(state_headers) !! (l +ₗ i) = None) →
  interp es σ ts ==∗
    interp es (state_alloc l (Header tag (length vs)) vs σ) ts ∗
    l ↦ₕ□ Header tag (length vs) ∗
    ([∗ list] i ↦ v ∈ vs, (l +ₗ Z.of_nat i) ↦ v) ∗
    (* Orphan token: only when vs = [] (size-0 block has no cell to
       carry [loc_tok1 l]). For non-empty [vs] the token at [l] is
       already bundled into the cell at offset 0. *)
    (match vs with [] => loc_tok1 l | _ :: _ => emp end)%I.
Proof.
  iIntros (Hlh Hl_heap Hheap Hhdrs) "(%Hlen & Hheap & Hhdrs & Hauth & Hloc & Hls & Htr)".
  iMod (gen_heap_alloc _ l (Header tag (length vs)) with "Hhdrs") as "(Hhdrs & Hl & _)"; first done.
  iMod (pointsto_persist with "Hl") as "#Hl".
  iMod (gen_heap_alloc_big _ (chunk l vs) with "Hheap")
    as "(Hheap & Hcells & _)".
  { apply chunk_map_disjoint. done. }
  assert (Hnew_disj : ({[l]} ∪ dom (chunk l vs))
                      ## (dom σ.(state_heap) ∪ dom σ.(state_headers))).
  { apply elem_of_disjoint. intros k Hk_new Hk_old.
    apply elem_of_union in Hk_new as [Hk_new|Hk_new].
    - apply elem_of_singleton in Hk_new; subst k.
      apply elem_of_union in Hk_old as [Hin|Hin];
      apply elem_of_dom in Hin as [? Hx]; congruence.
    - apply elem_of_dom in Hk_new as [w Hk_new].
      apply chunk_lookup in Hk_new as (j & Hj0 & -> & Hjvs).
      apply lookup_lt_Some in Hjvs.
      apply elem_of_union in Hk_old as [Hin|Hin];
      apply elem_of_dom in Hin as [? Hx].
      + rewrite -(Z2Nat.id _ Hj0) in Hx. rewrite (Hheap _ Hjvs) in Hx. congruence.
      + rewrite -(Z2Nat.id _ Hj0) in Hx. rewrite (Hhdrs _ Hjvs) in Hx. congruence. }
  iMod (loc_alloc _ ({[l]} ∪ dom (chunk l vs)) with "Hls") as "[Hls Hnewtoks]"; first done.
  iAssert (interp es (state_alloc l (Header tag (length vs)) vs σ) ts) with
    "[Hheap Hhdrs Hauth Hloc Hls Htr]" as "$".
  { rewrite /interp. iFrame "Htr". iFrame. iSplit; first done.
    rewrite /state_alloc /=.
    rewrite dom_union_L dom_insert_L.
    iEval (replace (dom σ.(state_heap) ∪ dom σ.(state_headers) ∪
                    ({[l]} ∪ dom (chunk l vs)))
              with (dom (chunk l vs) ∪ dom σ.(state_heap) ∪
                    ({[l]} ∪ dom σ.(state_headers))) by set_solver) in "Hls".
    iFrame. }
  iModIntro. iFrame "Hl".
  destruct vs as [|v0 vs'] eqn:Hvs.
  - (* size-0 block: no cells; emit [loc_tok1 l] as orphan *)
    simpl. rewrite dom_empty_L union_empty_r_L. rewrite /loc_tok1. iFrame.
  - (* non-empty: distribute [loc_tok (dom chunk)] across the cells *)
    iSplitL "Hcells Hnewtoks"; last done.
    rewrite -Hvs chunk_to_seq_pointsto.
    assert (Hlin : l ∈ dom (chunk l vs)).
    { apply elem_of_dom. rewrite Hvs /=.
      rewrite -(location_add_0 l) lookup_insert_eq. eauto. }
    replace ({[l]} ∪ dom (chunk l vs)) with (dom (chunk l vs))
      by set_solver.
    iPoseProof (loc_tok_chunk_distribute with "Hnewtoks") as "Hnewtoks".
    iCombine "Hcells Hnewtoks" as "Hcells".
    rewrite -big_sepL_sep.
    iApply (big_sepL_mono with "Hcells").
    iIntros (i x _) "[Hp Ht]". iFrame.
Qed.

Lemma interp_get_field l es σ ts dq v :
  interp es σ ts -∗ l ↦{dq} v -∗ ⌜σ.(state_heap) !! l = Some v⌝.
Proof.
  iIntros "(_ & Hheap & _) [Hl _]".
  by iDestruct (gen_heap_valid with "Hheap Hl") as %Hlook.
Qed.

Lemma interp_get_field_header l es σ ts dq hdr :
  interp es σ ts -∗ l ↦ₕ{dq} hdr -∗ ⌜σ.(state_headers) !! l = Some hdr⌝.
Proof.
  iIntros "(_ & _ & Hhdrs & _) Hl".
  by iDestruct (gen_heap_valid with "Hhdrs Hl") as %Hlook.
Qed.

Lemma interp_set_field l es σ ts v w :
  interp es σ ts -∗ l ↦ v ==∗
    ⌜σ.(state_heap) !! l = Some v⌝ ∗
    interp es (state_set_location l w σ) ts ∗
    l ↦ w.
Proof.
  iIntros "(%Hlen & Hheap & Hhdrs & Hsplit & Hloc & Hls) [Hl Htok]".
  iDestruct (gen_heap_valid with "Hheap Hl") as %Hlook.
  iMod (gen_heap_update _ _ _ w with "Hheap Hl") as "[Hheap Hl]".
  assert (l ∈ dom σ.(state_heap)) by (apply elem_of_dom; eauto).
  iModIntro. iSplit; first done.
  rewrite /mz_pointsto. iFrame "Hl Htok".
  rewrite /interp /state_set_location /state_update_heap /= dom_insert_L.
  replace ({[l]} ∪ dom σ.(state_heap) ∪ dom σ.(state_headers))
       with (dom σ.(state_heap) ∪ dom σ.(state_headers)) by set_solver.
  iFrame. done.
Qed.

(** Unfold a block into its (existentially-tagged) header and cells. *)
Lemma mz_block_unfold l dq vs :
  l ↦∗{dq} vs ⊣⊢
    ∃ tag, l ↦ₕ□ Header tag (length vs) ∗
           [∗ list] i ↦ v ∈ vs, (l +ₗ Z.of_nat i) ↦{dq} v.
Proof. done. Qed.

(** A block exposes its (persistent) header; [vs]'s length is the block size. *)
Lemma mz_block_header l dq vs :
  l ↦∗{dq} vs -∗ ∃ tag, l ↦ₕ□ Header tag (length vs).
Proof. iIntros "(%tag & #Hh & _)". by iExists tag. Qed.

(** In-bounds cell access at a [Z] offset, staying in [l +ₗ fld] form
    (matching the operational [base_step] field rules). *)
Lemma mz_block_cell_acc_Z l dq vs (fld : Z) v :
  (0 ≤ fld)%Z →
  vs !! Z.to_nat fld = Some v →
  l ↦∗{dq} vs -∗
    (l +ₗ fld) ↦{dq} v ∗
    (∀ w, (l +ₗ fld) ↦{dq} w -∗ l ↦∗{dq} <[Z.to_nat fld := w]> vs).
Proof.
  intros Hfld Hidx.
  replace (l +ₗ fld) with (l +ₗ Z.of_nat (Z.to_nat fld))
    by (rewrite Z2Nat.id //).
  iIntros "(%tag & #Hh & Hcells)".
  iDestruct (big_sepL_insert_acc with "Hcells") as "[$ Hclose]"; first done.
  iIntros (w) "Hw". iExists tag.
  rewrite length_insert. iFrame "Hh".
  by iApply "Hclose".
Qed.

(** From [interp] and a block at [l], an in-bounds field offset yields the
    [wf_access] witness: the header at [l] exists and the offset is in range. *)
Lemma interp_block_wf_access l es σ ts dq vs (fld : Z) :
  (0 ≤ fld < Z.of_nat (length vs))%Z →
  interp es σ ts -∗ l ↦∗{dq} vs -∗
    ⌜∃ hdr, σ.(state_headers) !! l = Some hdr ∧
            (0 ≤ fld < Z.of_nat (header_size hdr))%Z⌝.
Proof.
  iIntros (Hfld) "Hi Hblk".
  iDestruct (mz_block_header with "Hblk") as "(%tag & Hh)".
  iDestruct (interp_get_field_header with "Hi Hh") as %Hlook.
  iPureIntro. exists (Header tag (length vs)). done.
Qed.

(** Header-only [wf_access] witness: the persistent header alone (and an
    in-range offset) already certifies the access, without owning the
    whole block. Used by the header-aware cell rules (and so by the array
    specs), which carry the header [l ↦ₕ□ hdr] alongside individual cells. *)
Lemma interp_header_wf_access l es σ ts dqh hdr (fld : Z) :
  (0 ≤ fld < Z.of_nat (header_size hdr))%Z →
  interp es σ ts -∗ l ↦ₕ{dqh} hdr -∗
    ⌜∃ hdr', σ.(state_headers) !! l = Some hdr' ∧
             (0 ≤ fld < Z.of_nat (header_size hdr'))%Z⌝.
Proof.
  iIntros (Hfld) "Hi Hh".
  iDestruct (interp_get_field_header with "Hi Hh") as %Hlook.
  iPureIntro. exists hdr. done.
Qed.

End interp.

Module Initialization.

Definition seqlogΣ : gFunctors :=
  #[ invΣ;
     gen_heapΣ location val;
     gen_heapΣ location header;
     ghost_mapΣ nat expr;
     ghost_mapΣ nat val;
     savedPropΣ;
     GFunctor (authR (gset_disjUR location));
     ghost_mapΣ unit (list observation) ].

Class seqlogPreG (Σ : gFunctors) :=
{ sl1 : invGpreS Σ;
  sl2 : gen_heapGpreS location val Σ;
  sl2h : gen_heapGpreS location header Σ;
  sl3 : ghost_mapG Σ nat expr;
  sl3l : ghost_mapG Σ nat val;
  sl4 : savedPropG Σ;
  sl5 : inG Σ (authR (gset_disjUR location));
  sl6 : ghost_mapG Σ unit (list observation) }.

#[global] Existing Instance sl1.
#[local] Existing Instance sl2.
#[local] Existing Instance sl2h.
#[local] Existing Instance sl3.
#[local] Existing Instance sl3l.
#[local] Existing Instance sl4.
#[global] Existing Instance sl5.
#[local] Existing Instance sl6.

Global Instance subG_seqlogPreG Σ :
  subG seqlogΣ Σ → seqlogPreG Σ.
Proof. solve_inG. Qed.

Global Instance seqlogPreG_seqlogΣ : seqlogPreG seqlogΣ.
Proof. eauto with typeclass_instances. Qed.

Lemma seqlog_init `{!seqlogPreG Σ, hinv:!invGS_gen HasLc Σ} e σ v0 :
  σ.(state_locals) = [v0] →
  ⊢ |==> ∃ hi : seqlogGS Σ, ⌜@iinvgs Σ hi = hinv⌝ ∗
  running 0 e ∗ local 0 v0 ∗
  trace_model [] ∗
  (∀ P, |==> interp [e] σ [] ∗ saved_prop_own (savedPropG0:=isprop) γinit DfracDiscarded P).
Proof.
  intros Hloc.
  rewrite /interp /running /local.
  iMod (gen_heap_init σ.(state_heap)) as "[%Gh (Hheap & _)]".
  iMod (gen_heap_init σ.(state_headers)) as "[%Ghh (Hhdrs & _)]".
  iMod (@ghost_map_alloc_empty _ nat expr _ _ _) as "[%γs Hsplit]".
  iMod (ghost_map_insert 0 e with "Hsplit") as "[Hsplit Hrun]"; first done.
  iMod (@ghost_map_alloc_empty _ nat val _ _ _) as "[%γl Hloc]".
  iMod (ghost_map_insert 0 v0 with "Hloc") as "[Hloc Hv0]"; first done.
  iMod (saved_prop_alloc False (DfracOwn 1)) as "[%γi HP]"; first done.
  iMod (own_alloc (● GSet (dom σ.(state_heap) ∪ dom σ.(state_headers))))
    as "[%γls Hls]".
  { apply auth_auth_valid. done. }
  iMod (ghost_map_alloc {[() := @nil observation]}) as "[%γp [Hpauth Hpfrags]]".
  iExists (@SeqlogGS Σ hinv Gh Ghh γs _ γl _ _ γi _ γls _ γp). iFrame.
  rewrite big_sepM_singleton. iFrame "Hpfrags".
  iSplitR; first done. iModIntro.
  iIntros (P).
  iMod (saved_prop_update P with "HP") as "HP".
  iMod (saved_prop_persist with "HP") as "#HP".
  iFrame "HP". iModIntro.
  iSplitR.
  { iPureIntro. simpl. rewrite Hloc //. }
  rewrite Hloc /=. iFrame.
Qed.

End Initialization.
