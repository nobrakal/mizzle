From stdpp Require Import relations.
From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi.lib Require Import fixpoint_mono.

From mizzle.lang Require Import instances.

From mizzle.logic Require Import interp goal adequacy translate decompose
  wf_access.

(** All the reasons a [wf_access]-guarded [base_step] cannot fire: either
    the step itself is impossible, or [wf_access σ r] fails (the [*_no_hdr]
    and [*_oob] cases).  The other memory cases (GetField/SetField/Xchg/CAS/
    FAA) cover heap cells that may be absent even when [wf_access]
    certifies the header exists and the field index is in bounds.  There is no [Emit] case: [Emit #v]
    always steps, so it is never stuck. *)
Inductive base_stuck (tid : thread_id) (e : expr) (σ : state) : Prop :=
  (* App (Val v) (Val w) with v not a ValRecs *)
  | base_stuck_call v w :
      e = App (Val v) (Val w) →
      (match v with ValRecs _ _ => False | _ => True end) →
      base_stuck tid e σ
  (* ValRecs i recs applied to v, but index i missing from recs *)
  | base_stuck_app i recs v :
      e = App (Val (ValRecs i recs)) (Val v) →
      recs !! i = None →
      base_stuck tid e σ
  (* Unop: eval_unop fails *)
  | base_stuck_unop op v :
      e = Unop op (Val v) →
      eval_unop op v = None →
      base_stuck tid e σ
  (* Binop: eval_binop fails *)
  | base_stuck_binop op v1 v2 :
      e = Binop op (Val v1) (Val v2) →
      eval_binop op v1 v2 = None →
      base_stuck tid e σ
  (* If (Val v) _ _ with v not a bool *)
  | base_stuck_if v e1 e2 :
      e = If (Val v) e1 e2 →
      (match v with ValBool _ => False | _ => True end) →
      base_stuck tid e σ
  (* For (Val v1) (Val v2) _ with v1/v2 not both ValInt *)
  | base_stuck_for v1 v2 e' :
      e = For (Val v1) (Val v2) e' →
      (match v1, v2 with ValInt _, ValInt _ => False | _, _ => True end) →
      base_stuck tid e σ
  (* Alloc: wrong argument types *)
  | base_stuck_alloc_bad v1 v2 :
      e = Alloc (Val v1) (Val v2) →
      (match v1 with
       | ValInt _ => match v2 with ValInt _ => False | _ => True end
       | _ => True end) →
      base_stuck tid e σ
  (* Alloc: negative tag or negative size *)
  | base_stuck_alloc_neg z n :
      e = Alloc (Val (ValInt z)) (Val (ValInt n)) →
      (z < 0 ∨ n < 0)%Z →
      base_stuck tid e σ
  (* Block Mutable tag []: empty mutable block *)
  | base_stuck_block_mutable tag :
      e = Block Mutable tag [] →
      base_stuck tid e σ
  (* Match (Val v) _ _ _ with v not a loc or block *)
  | base_stuck_match_bad v x e' brs :
      e = Match (Val v) x e' brs →
      (match v with
       | ValLoc _ => False | ValBlock _ _ _ => False | _ => True end) →
      base_stuck tid e σ
  (* Match mutable: l not allocated *)
  | base_stuck_match_mutable_no_hdr l x e' brs :
      e = Match (Val (ValLoc l)) x e' brs →
      state_headers σ !! l = None →
      base_stuck tid e σ
  (* Match mutable: no matching branch *)
  | base_stuck_match_mutable_no_branch l hdr x e' brs :
      e = Match (Val (ValLoc l)) x e' brs →
      state_headers σ !! l = Some hdr →
      eval_match (header_tag hdr) (header_size hdr) (SubjectLoc l) x e' brs = None →
      base_stuck tid e σ
  (* Match immutable: no matching branch *)
  | base_stuck_match_immutable_no_branch gen tag vs x e' brs :
      e = Match (Val (ValBlock gen tag vs)) x e' brs →
      eval_match tag (length vs) (SubjectBlock gen vs) x e' brs = None →
      base_stuck tid e σ
  (* GetTag (Val v) with v not a loc or block *)
  | base_stuck_gettag_bad v :
      e = GetTag (Val v) →
      (match v with
       | ValLoc _ => False | ValBlock _ _ _ => False | _ => True end) →
      base_stuck tid e σ
  (* GetTag mutable: l not allocated *)
  | base_stuck_gettag_mutable_no_hdr l :
      e = GetTag (Val (ValLoc l)) →
      state_headers σ !! l = None →
      base_stuck tid e σ
  (* GetTag immutable: empty block has no tag *)
  | base_stuck_gettag_immutable_empty gen tag :
      e = GetTag (Val (ValBlock gen tag [])) →
      base_stuck tid e σ
  (* GetSize (Val v) with v not a loc or block *)
  | base_stuck_getsize_bad v :
      e = GetSize (Val v) →
      (match v with
       | ValLoc _ => False | ValBlock _ _ _ => False | _ => True end) →
      base_stuck tid e σ
  (* GetSize mutable: l not allocated *)
  | base_stuck_getsize_mutable_no_hdr l :
      e = GetSize (Val (ValLoc l)) →
      state_headers σ !! l = None →
      base_stuck tid e σ
  (* GetSize immutable: empty block has no size *)
  | base_stuck_getsize_immutable_empty gen tag :
      e = GetSize (Val (ValBlock gen tag [])) →
      base_stuck tid e σ
  (* GetField (Val v1) (Val v2): wrong argument types *)
  | base_stuck_get_field_bad atm v1 v2 :
      e = GetField atm (Val v1) (Val v2) →
      (match v1 with
       | ValLoc _     => match v2 with ValInt _ => False | _ => True end
       | ValBlock _ _ _ => match v2 with ValInt _ => False | _ => True end
       | _ => True end) →
      base_stuck tid e σ
  (* GetField mutable: location not allocated (wf_access fails) *)
  | base_stuck_get_field_loc_no_hdr atm l fld :
      e = GetField atm (Val (ValLoc l)) (Val (ValInt fld)) →
      state_headers σ !! l = None →
      base_stuck tid e σ
  (* GetField mutable: field index out of bounds (wf_access fails) *)
  | base_stuck_get_field_loc_oob atm l fld hdr :
      e = GetField atm (Val (ValLoc l)) (Val (ValInt fld)) →
      state_headers σ !! l = Some hdr →
      ¬ (0 ≤ fld < header_size hdr)%Z →
      base_stuck tid e σ
  (* GetField mutable: heap cell absent (wf_access holds but cell missing) *)
  | base_stuck_get_field_loc atm l fld hdr :
      e = GetField atm (Val (ValLoc l)) (Val (ValInt fld)) →
      state_headers σ !! l = Some hdr →
      (0 ≤ fld < header_size hdr)%Z →
      state_heap σ !! (l +ₗ fld) = None →
      base_stuck tid e σ
  (* GetField immutable: field index out of range (no matching nat fld) *)
  | base_stuck_get_field_block atm gen tag vs fld :
      e = GetField atm (Val (ValBlock gen tag vs)) (Val (ValInt fld)) →
      (∀ n : nat, Z.of_nat n = fld → vs !! n = None) →
      base_stuck tid e σ
  (* SetField (Val v1) (Val v2) (Val v3): wrong argument types *)
  | base_stuck_set_field_bad atm v1 v2 v3 :
      e = SetField atm (Val v1) (Val v2) (Val v3) →
      (match v1, v2 with ValLoc _, ValInt _ => False | _, _ => True end) →
      base_stuck tid e σ
  (* SetField mutable: location not allocated (wf_access fails) *)
  | base_stuck_set_field_no_hdr atm l fld v :
      e = SetField atm (Val (ValLoc l)) (Val (ValInt fld)) (Val v) →
      state_headers σ !! l = None →
      base_stuck tid e σ
  (* SetField mutable: field index out of bounds (wf_access fails) *)
  | base_stuck_set_field_oob atm l fld v hdr :
      e = SetField atm (Val (ValLoc l)) (Val (ValInt fld)) (Val v) →
      state_headers σ !! l = Some hdr →
      ¬ (0 ≤ fld < header_size hdr)%Z →
      base_stuck tid e σ
  (* SetField mutable: heap cell absent (wf_access holds but cell missing) *)
  | base_stuck_set_field atm l fld v hdr :
      e = SetField atm (Val (ValLoc l)) (Val (ValInt fld)) (Val v) →
      state_headers σ !! l = Some hdr →
      (0 ≤ fld < header_size hdr)%Z →
      state_heap σ !! (l +ₗ fld) = None →
      base_stuck tid e σ
  (* Xchg (Val v1) (Val v2): wrong type for v1 *)
  | base_stuck_xchg_bad v1 v2 :
      e = Xchg (Val v1) (Val v2) →
      (match v1 with ValTuple [ValLoc _; ValInt _] => False | _ => True end) →
      base_stuck tid e σ
  (* Xchg: location not allocated (wf_access fails) *)
  | base_stuck_xchg_no_hdr l fld v :
      e = Xchg (Val (ValTuple [ValLoc l; ValInt fld])) (Val v) →
      state_headers σ !! l = None →
      base_stuck tid e σ
  (* Xchg: field index out of bounds (wf_access fails) *)
  | base_stuck_xchg_oob l fld v hdr :
      e = Xchg (Val (ValTuple [ValLoc l; ValInt fld])) (Val v) →
      state_headers σ !! l = Some hdr →
      ¬ (0 ≤ fld < header_size hdr)%Z →
      base_stuck tid e σ
  (* Xchg: heap cell absent (wf_access holds but cell missing) *)
  | base_stuck_xchg l fld v hdr :
      e = Xchg (Val (ValTuple [ValLoc l; ValInt fld])) (Val v) →
      state_headers σ !! l = Some hdr →
      (0 ≤ fld < header_size hdr)%Z →
      state_heap σ !! (l +ₗ fld) = None →
      base_stuck tid e σ
  (* CAS (Val v0) (Val v1) (Val v2): wrong type for v0 *)
  | base_stuck_cas_bad v0 v1 v2 :
      e = CAS (Val v0) (Val v1) (Val v2) →
      (match v0 with ValTuple [ValLoc _; ValInt _] => False | _ => True end) →
      base_stuck tid e σ
  (* CAS: location not allocated (wf_access fails) *)
  | base_stuck_cas_no_hdr l fld v1 v2 :
      e = CAS (Val (ValTuple [ValLoc l; ValInt fld])) (Val v1) (Val v2) →
      state_headers σ !! l = None →
      base_stuck tid e σ
  (* CAS: field index out of bounds (wf_access fails) *)
  | base_stuck_cas_oob l fld v1 v2 hdr :
      e = CAS (Val (ValTuple [ValLoc l; ValInt fld])) (Val v1) (Val v2) →
      state_headers σ !! l = Some hdr →
      ¬ (0 ≤ fld < header_size hdr)%Z →
      base_stuck tid e σ
  (* CAS: heap cell absent (wf_access holds but cell missing) *)
  | base_stuck_cas l fld v1 v2 hdr :
      e = CAS (Val (ValTuple [ValLoc l; ValInt fld])) (Val v1) (Val v2) →
      state_headers σ !! l = Some hdr →
      (0 ≤ fld < header_size hdr)%Z →
      state_heap σ !! (l +ₗ fld) = None →
      base_stuck tid e σ
  (* FAA (Val v1) (Val v2): wrong argument types *)
  | base_stuck_faa_bad v1 v2 :
      e = FAA (Val v1) (Val v2) →
      (match v1 with
       | ValTuple [ValLoc _; ValInt _] =>
           match v2 with ValInt _ => False | _ => True end
       | _ => True end) →
      base_stuck tid e σ
  (* FAA: location not allocated (wf_access fails) *)
  | base_stuck_faa_no_hdr l fld n :
      e = FAA (Val (ValTuple [ValLoc l; ValInt fld])) (Val (ValInt n)) →
      state_headers σ !! l = None →
      base_stuck tid e σ
  (* FAA: field index out of bounds (wf_access fails) *)
  | base_stuck_faa_oob l fld n hdr :
      e = FAA (Val (ValTuple [ValLoc l; ValInt fld])) (Val (ValInt n)) →
      state_headers σ !! l = Some hdr →
      ¬ (0 ≤ fld < header_size hdr)%Z →
      base_stuck tid e σ
  (* FAA: heap cell absent (wf_access holds but cell missing) *)
  | base_stuck_faa_no_cell l fld n hdr :
      e = FAA (Val (ValTuple [ValLoc l; ValInt fld])) (Val (ValInt n)) →
      state_headers σ !! l = Some hdr →
      (0 ≤ fld < header_size hdr)%Z →
      state_heap σ !! (l +ₗ fld) = None →
      base_stuck tid e σ
  (* FAA: heap cell present but not an integer *)
  | base_stuck_faa_not_int l fld n v hdr :
      e = FAA (Val (ValTuple [ValLoc l; ValInt fld])) (Val (ValInt n)) →
      state_headers σ !! l = Some hdr →
      (0 ≤ fld < header_size hdr)%Z →
      state_heap σ !! (l +ₗ fld) = Some v →
      (∀ m : Z, v ≠ ValInt m) →
      base_stuck tid e σ
  (* GetLocal: thread has no local value *)
  | base_stuck_get_local :
      e = GetLocal →
      state_locals σ !! tid = None →
      base_stuck tid e σ
  (* SetLocal (Val v): thread has no local slot *)
  | base_stuck_set_local v :
      e = SetLocal (Val v) →
      state_locals σ !! tid = None →
      base_stuck tid e σ
  (* Var x: open term that cannot step *)
  | base_stuck_var x :
      e = Var x →
      base_stuck tid e σ.

Lemma deduce_base_stuck r p σ :
  to_val r = None ->
  sub_redexes_are_values r ->
  (∀ κ r' σ' es, base_step p r σ κ r' σ' es → wf_access σ r → False) ->
  base_stuck p r σ.
Proof.
  intros Hv Hredx Hstep.
  destruct r as [v | x | f x r | r1 r2 | x r1 r2 | op r | op r1 r2 | r1 r2
    | r1 r2 r3 | r1 r2 | r1 r2 r3 | r1 r2 | mut tag rs | r0 x r1 brs | r | r
    | atm r1 r2 | atm r1 r2 r3 | r1 r2 | r0 r1 r2 | r1 r2 | r | | r | r].
  - done.
  - eauto using base_stuck.
  - exfalso. eapply Hstep. { exact (base_step_rec p f x r σ). } exact I.
  - (* App r1 r2 *)
    have [v2 Hv2] : is_Some (to_val r2).
    { destruct (to_val r2) eqn:H; [by eauto|exfalso].
      discriminate (Hredx [CtxApp2 r1] r2 eq_refl H). }
    apply of_to_val in Hv2; subst r2.
    have [v1 Hv1] : is_Some (to_val r1).
    { destruct (to_val r1) eqn:H; [by eauto|exfalso].
      discriminate (Hredx [CtxApp1 v2] r1 eq_refl H). }
    apply of_to_val in Hv1; subst r1.
    destruct v1 as [lit | i recs | gen tag vs].
    + eapply base_stuck_call; [done|destruct lit; done].
    + destruct (recs !! i) as [rec|] eqn:Hi.
      * exfalso. eapply Hstep; [exact (base_step_app p i recs rec v2 σ Hi)|exact I].
      * eapply base_stuck_app; done.
    + eapply base_stuck_call; done.
  - (* Let x r1 r2 *)
    have [v1 Hv1] : is_Some (to_val r1).
    { destruct (to_val r1) eqn:H; [by eauto|exfalso].
      discriminate (Hredx [CtxLet x r2] r1 eq_refl H). }
    apply of_to_val in Hv1; subst r1.
    exfalso. eapply Hstep; [exact (base_step_let p x v1 r2 σ)|exact I].
  - (* Unop op r *)
    have [v Hval] : is_Some (to_val r).
    { destruct (to_val r) eqn:H; [by eauto|exfalso].
      discriminate (Hredx [CtxUnop op] r eq_refl H). }
    apply of_to_val in Hval; subst r.
    destruct (eval_unop op v) eqn:Heval.
    + exfalso. eapply Hstep; [exact (base_step_unop p op v v0 σ Heval)|exact I].
    + eapply base_stuck_unop; done.
  - (* Binop op r1 r2 *)
    have [v2 Hv2] : is_Some (to_val r2).
    { destruct (to_val r2) eqn:H; [by eauto|exfalso].
      discriminate (Hredx [CtxBinop2 op r1] r2 eq_refl H). }
    apply of_to_val in Hv2; subst r2.
    have [v1 Hv1] : is_Some (to_val r1).
    { destruct (to_val r1) eqn:H; [by eauto|exfalso].
      discriminate (Hredx [CtxBinop1 op v2] r1 eq_refl H). }
    apply of_to_val in Hv1; subst r1.
    destruct (eval_binop op v1 v2) eqn:Heval.
    + exfalso. eapply Hstep; [exact (base_step_binop p op v1 v2 v σ Heval)|exact I].
    + eapply base_stuck_binop; done.
  - (* Equal r1 r2 *)
    have [v2 Hv2] : is_Some (to_val r2).
    { destruct (to_val r2) eqn:H; [by eauto|exfalso].
      discriminate (Hredx [CtxEqual2 r1] r2 eq_refl H). }
    apply of_to_val in Hv2; subst r2.
    have [v1 Hv1] : is_Some (to_val r1).
    { destruct (to_val r1) eqn:H; [by eauto|exfalso].
      discriminate (Hredx [CtxEqual1 v2] r1 eq_refl H). }
    apply of_to_val in Hv1; subst r1.
    exfalso.
    destruct (val_similar_or_nonsimilar v1 v2) as [Hs|Hns].
    + eapply Hstep; [exact (base_step_equal_success p v1 v2 σ Hs)|exact I].
    + eapply Hstep; [exact (base_step_equal_fail p v1 v2 σ Hns)|exact I].
  - (* If r1 r2 r3 *)
    have [v1 Hv1] : is_Some (to_val r1).
    { destruct (to_val r1) eqn:H; [by eauto|exfalso].
      discriminate (Hredx [CtxIf r2 r3] r1 eq_refl H). }
    apply of_to_val in Hv1; subst r1.
    destruct v1 as [[b|n|l|]|i recs|gen tag vs]; try (eapply base_stuck_if; done).
    exfalso. eapply Hstep; [exact (base_step_if p b r2 r3 σ)|exact I].
  - (* While r1 r2 *)
    exfalso. eapply Hstep; [exact (base_step_while p r1 r2 σ)|exact I].
  - (* For r1 r2 r3 *)
    have [v1 Hv1] : is_Some (to_val r1).
    { destruct (to_val r1) eqn:H; [by eauto|exfalso].
      discriminate (Hredx [CtxFor1 r2 r3] r1 eq_refl H). }
    apply of_to_val in Hv1; subst r1.
    have [v2 Hv2] : is_Some (to_val r2).
    { destruct (to_val r2) eqn:H; [by eauto|exfalso].
      discriminate (Hredx [CtxFor2 v1 r3] r2 eq_refl H). }
    apply of_to_val in Hv2; subst r2.
    destruct v1 as [[b1|n1|l1|]|i1 recs1|gen1 tag1 vs1];
    destruct v2 as [[b2|n2|l2|]|i2 recs2|gen2 tag2 vs2];
    try (eapply base_stuck_for; simpl; done).
    exfalso. eapply Hstep; [exact (base_step_for p n1 n2 r3 σ)|exact I].
  - (* Alloc r1 r2 *)
    have [v2 Hv2] : is_Some (to_val r2).
    { destruct (to_val r2) eqn:H; [by eauto|exfalso].
      discriminate (Hredx [CtxAlloc2 r1] r2 eq_refl H). }
    apply of_to_val in Hv2; subst r2.
    have [v1 Hv1] : is_Some (to_val r1).
    { destruct (to_val r1) eqn:H; [by eauto|exfalso].
      discriminate (Hredx [CtxAlloc1 v2] r1 eq_refl H). }
    apply of_to_val in Hv1; subst r1.
    destruct v1 as [[b1|z|l1|]|i1 recs1|gen1 tag1 vs1];
    destruct v2 as [[b2|n|l2|]|i2 recs2|gen2 tag2 vs2];
    try (eapply base_stuck_alloc_bad; simpl; done).
    destruct (decide (0 ≤ z)%Z) as [Hz|Hz]; destruct (decide (0 ≤ n)%Z) as [Hn|Hn].
    + exfalso. eapply Hstep; [|exact I].
      have := base_step_alloc p (Z.to_nat z) n σ (state_fresh σ) Hn (state_alloc_condition_fresh _ σ).
      by rewrite Z2Nat.id.
    + eapply base_stuck_alloc_neg; [done|right; lia].
    + eapply base_stuck_alloc_neg; [done|left; lia].
    + eapply base_stuck_alloc_neg; [done|left; lia].
  - (* Block mut tag rs *)
    have Hsb : split_block rs = None.
    { destruct (split_block rs) as [[[pre hole] suf]|] eqn:H; [|done].
      apply split_block_sound in H as [Hrs Hhole].
      exfalso.
      have Heq : Block mut tag rs = fill [CtxBlock mut tag pre suf] hole.
      { simpl. f_equal. exact Hrs. }
      have := Hredx [CtxBlock mut tag pre suf] hole Heq Hhole.
      discriminate. }
    have split_block_none_of_vals : ∀ es, split_block es = None → ∃ vs, es = of_vals vs.
    { intro es. induction es as [|r es' IH].
      - intros _. exists []. done.
      - intros Hsb'.
        simpl in Hsb'.
        destruct (split_block es') as [[[pre hole] suf]|] eqn:Hrec.
        + discriminate.
        + have [vs' Hvs'] := IH eq_refl.
          destruct (to_val r) as [v|] eqn:Hr.
          * apply of_to_val in Hr; subst r; subst es'.
            exists (v :: vs'). done.
          * subst es'. rewrite to_of_vals in Hsb'. discriminate. }
    have [vs Hvs] := split_block_none_of_vals rs Hsb.
    subst rs.
    have wf_access_block : wf_access σ (Block mut tag (of_vals vs)).
    { unfold wf_access.
      have -> : (decompose (Block mut tag (of_vals vs))).2 = Block mut tag (of_vals vs).
      { unfold decompose. simpl. rewrite split_block_of_vals. done. }
      exact I. }
    destruct mut.
    + destruct vs as [|v vs'].
      * eapply base_stuck_block_mutable. done.
      * exfalso. eapply Hstep.
        { apply base_step_block_mutable'. { simpl; lia. } done. }
        exact wf_access_block.
    + exfalso. eapply Hstep.
      { exact (base_step_block_immutable_nongenerative p tag (of_vals vs) vs σ eq_refl). }
      exact wf_access_block.
    + exfalso. eapply Hstep.
      { exact (base_step_block_immutable_generative_weak p tag (of_vals vs) vs σ eq_refl). }
      exact wf_access_block.
    + exfalso. eapply Hstep.
      { exact (base_step_block_immutable_generative_strong p tag (of_vals vs) vs σ inhabitant eq_refl). }
      exact wf_access_block.
  - (* Match r0 x r1 brs *)
    have [v0 Hv0] : is_Some (to_val r0).
    { destruct (to_val r0) eqn:H; [by eauto|exfalso].
      discriminate (Hredx [CtxMatch x r1 brs] r0 eq_refl H). }
    apply of_to_val in Hv0; subst r0.
    destruct v0 as [[b|n|l|]|i recs|gen tag vs];
      try (eapply base_stuck_match_bad; done).
    + (* ValLoc l *)
      destruct (state_headers σ !! l) as [hdr|] eqn:Hhdr.
      * destruct (eval_match (header_tag hdr) (header_size hdr) (SubjectLoc l) x r1 brs) as [e'|] eqn:Hem.
        -- exfalso. eapply Hstep; [exact (base_step_match_mutable p l hdr x r1 brs e' σ Hhdr Hem)|exact I].
        -- eapply base_stuck_match_mutable_no_branch; done.
      * eapply base_stuck_match_mutable_no_hdr; done.
    + (* ValBlock gen tag vs *)
      destruct (eval_match tag (length vs) (SubjectBlock gen vs) x r1 brs) as [e'|] eqn:Hem.
      * exfalso. eapply Hstep; [exact (base_step_match_immutable p gen tag vs x r1 brs e' σ Hem)|exact I].
      * eapply base_stuck_match_immutable_no_branch; done.
  - (* GetTag r *)
    have [v Hv0] : is_Some (to_val r).
    { destruct (to_val r) eqn:H; [by eauto|exfalso].
      discriminate (Hredx [CtxGetTag] r eq_refl H). }
    apply of_to_val in Hv0; subst r.
    destruct v as [[b|n|l|]|i recs|gen tag vs];
      try (eapply base_stuck_gettag_bad; done).
    + (* ValLoc l *)
      destruct (state_headers σ !! l) as [hdr|] eqn:Hhdr.
      * exfalso. eapply Hstep; [exact (base_step_get_tag_mutable p l hdr σ Hhdr)|exact I].
      * eapply base_stuck_gettag_mutable_no_hdr; done.
    + (* ValBlock gen tag vs *)
      destruct vs as [|v vs'].
      * eapply base_stuck_gettag_immutable_empty; done.
      * exfalso. eapply Hstep; [apply (base_step_get_tag_immutable p gen tag (v :: vs') σ); simpl; lia|exact I].
  - (* GetSize r *)
    have [v Hv0] : is_Some (to_val r).
    { destruct (to_val r) eqn:H; [by eauto|exfalso].
      discriminate (Hredx [CtxGetSize] r eq_refl H). }
    apply of_to_val in Hv0; subst r.
    destruct v as [[b|n|l|]|i recs|gen tag vs];
      try (eapply base_stuck_getsize_bad; done).
    + (* ValLoc l *)
      destruct (state_headers σ !! l) as [hdr|] eqn:Hhdr.
      * exfalso. eapply Hstep; [exact (base_step_get_size_mutable p l hdr σ Hhdr)|exact I].
      * eapply base_stuck_getsize_mutable_no_hdr; done.
    + (* ValBlock gen tag vs *)
      destruct vs as [|v vs'].
      * eapply base_stuck_getsize_immutable_empty; done.
      * exfalso. eapply Hstep; [apply (base_step_get_size_immutable p gen tag (v :: vs') σ); simpl; lia|exact I].
  - (* GetField r1 r2 *)
    have [v2 Hv2] : is_Some (to_val r2).
    { destruct (to_val r2) eqn:H; [by eauto|exfalso].
      discriminate (Hredx [CtxGetField2 atm r1] r2 eq_refl H). }
    apply of_to_val in Hv2; subst r2.
    have [v1 Hv1] : is_Some (to_val r1).
    { destruct (to_val r1) eqn:H; [by eauto|exfalso].
      discriminate (Hredx [CtxGetField1 atm v2] r1 eq_refl H). }
    apply of_to_val in Hv1; subst r1.
    destruct v1 as [[b1|n1|l|]|i1 recs1|gen tag vs];
    destruct v2 as [[b2|fld|l2|]|i2 recs2|gen2 tag2 vs2];
    try (eapply base_stuck_get_field_bad; simpl; done).
    + (* ValLoc l, ValInt fld *)
      destruct (state_headers σ !! l) as [hdr|] eqn:Hhdr.
      * destruct (decide (0 ≤ fld < header_size hdr)%Z) as [Hbd|Hbd].
        -- destruct (state_heap σ !! (l +ₗ fld)) as [w|] eqn:Hcell.
           ++ exfalso. eapply Hstep; [exact (base_step_get_field_mutable p atm l fld w σ Hcell)|].
              unfold wf_access; simpl. exists hdr. done.
           ++ eapply base_stuck_get_field_loc; done.
        -- eapply base_stuck_get_field_loc_oob; done.
      * eapply base_stuck_get_field_loc_no_hdr; done.
    + (* ValBlock gen tag vs, ValInt fld *)
      destruct (decide (0 ≤ fld)%Z) as [Hfld|Hfld].
      * destruct (vs !! Z.to_nat fld) as [w|] eqn:Hvn.
        -- exfalso. eapply Hstep; [|exact I].
           have Hstep' := base_step_get_field_immutable p atm gen tag vs (Z.to_nat fld) w σ Hvn.
           rewrite Z2Nat.id in Hstep'; [exact Hstep'|exact Hfld].
        -- eapply base_stuck_get_field_block; [done|].
           intros n Hn. assert (n = Z.to_nat fld) as -> by lia. exact Hvn.
      * eapply base_stuck_get_field_block; [done|].
        intros n Hn. exfalso. lia.
  - (* SetField r1 r2 r3 *)
    have [v3 Hv3] : is_Some (to_val r3).
    { destruct (to_val r3) eqn:H; [by eauto|exfalso].
      discriminate (Hredx [CtxSetField3 atm r1 r2] r3 eq_refl H). }
    apply of_to_val in Hv3; subst r3.
    have [v2 Hv2] : is_Some (to_val r2).
    { destruct (to_val r2) eqn:H; [by eauto|exfalso].
      discriminate (Hredx [CtxSetField2 atm r1 v3] r2 eq_refl H). }
    apply of_to_val in Hv2; subst r2.
    have [v1 Hv1] : is_Some (to_val r1).
    { destruct (to_val r1) eqn:H; [by eauto|exfalso].
      discriminate (Hredx [CtxSetField1 atm v2 v3] r1 eq_refl H). }
    apply of_to_val in Hv1; subst r1.
    destruct v1 as [[b1|n1|l|]|i1 recs1|gen tag vs];
    destruct v2 as [[b2|fld|l2|]|i2 recs2|gen2 tag2 vs2];
    try (eapply base_stuck_set_field_bad; simpl; done).
    destruct (state_headers σ !! l) as [hdr|] eqn:Hhdr.
    + destruct (decide (0 ≤ fld < header_size hdr)%Z) as [Hbd|Hbd].
      * destruct (state_heap σ !! (l +ₗ fld)) as [w|] eqn:Hcell.
        -- exfalso. eapply Hstep; [apply (base_step_set_field p atm l fld v3 σ); rewrite Hcell; by eauto|].
           unfold wf_access; simpl. exists hdr. done.
        -- eapply base_stuck_set_field; done.
      * eapply base_stuck_set_field_oob; done.
    + eapply base_stuck_set_field_no_hdr; done.
  - (* Xchg r1 r2 *)
    have [v2 Hv2] : is_Some (to_val r2).
    { destruct (to_val r2) eqn:H; [by eauto|exfalso].
      discriminate (Hredx [CtxXchg2 r1] r2 eq_refl H). }
    apply of_to_val in Hv2; subst r2.
    have [v1 Hv1] : is_Some (to_val r1).
    { destruct (to_val r1) eqn:H; [by eauto|exfalso].
      discriminate (Hredx [CtxXchg1 v2] r1 eq_refl H). }
    apply of_to_val in Hv1; subst r1.
    destruct v1 as [lit|i recs|gen tag vs]; try (eapply base_stuck_xchg_bad; done).
    destruct gen as [bid|]; [eapply base_stuck_xchg_bad; done|].
    destruct tag as [|tag']; [|eapply base_stuck_xchg_bad; done].
    destruct vs as [| [[ba|na|l|]|ia ra|ga ta vsa] [| [[bb|fld|lb|]|ib rb|gb tb vsb] [|c vs']]];
    try (eapply base_stuck_xchg_bad; [reflexivity|exact I]).
    destruct (state_headers σ !! l) as [hdr|] eqn:Hhdr.
    + destruct (decide (0 ≤ fld < header_size hdr)%Z) as [Hbd|Hbd].
      * destruct (state_heap σ !! (l +ₗ fld)) as [w|] eqn:Hcell.
        -- exfalso. eapply Hstep; [exact (base_step_xchg p l fld v2 w σ Hcell)|].
           unfold wf_access; simpl. exists hdr. done.
        -- eapply base_stuck_xchg; done.
      * eapply base_stuck_xchg_oob; done.
    + eapply base_stuck_xchg_no_hdr; done.
  - (* CAS r0 r1 r2 *)
    have [v2 Hv2] : is_Some (to_val r2).
    { destruct (to_val r2) eqn:H; [by eauto|exfalso].
      discriminate (Hredx [CtxCAS2 r0 r1] r2 eq_refl H). }
    apply of_to_val in Hv2; subst r2.
    have [v1 Hv1] : is_Some (to_val r1).
    { destruct (to_val r1) eqn:H; [by eauto|exfalso].
      discriminate (Hredx [CtxCAS1 r0 v2] r1 eq_refl H). }
    apply of_to_val in Hv1; subst r1.
    have [v0 Hv0] : is_Some (to_val r0).
    { destruct (to_val r0) eqn:H; [by eauto|exfalso].
      discriminate (Hredx [CtxCAS0 v1 v2] r0 eq_refl H). }
    apply of_to_val in Hv0; subst r0.
    destruct v0 as [lit|i recs|gen tag vs]; try (eapply base_stuck_cas_bad; done).
    destruct gen as [bid|]; [eapply base_stuck_cas_bad; done|].
    destruct tag as [|tag']; [|eapply base_stuck_cas_bad; done].
    destruct vs as [| [[ba|na|l|]|ia ra|ga ta vsa] [| [[bb|fld|lb|]|ib rb|gb tb vsb] [|c vs']]];
    try (eapply base_stuck_cas_bad; [reflexivity|exact I]).
    destruct (state_headers σ !! l) as [hdr|] eqn:Hhdr.
    + destruct (decide (0 ≤ fld < header_size hdr)%Z) as [Hbd|Hbd].
      * destruct (state_heap σ !! (l +ₗ fld)) as [w|] eqn:Hcell.
        -- exfalso. destruct (val_similar_or_nonsimilar w v1) as [Hs|Hns].
           ++ eapply Hstep; [exact (base_step_cas_success p l fld v1 v2 w σ Hcell Hs)|unfold wf_access; simpl; exists hdr; done].
           ++ eapply Hstep; [exact (base_step_cas_fail p l fld v1 v2 w σ Hcell Hns)|unfold wf_access; simpl; exists hdr; done].
        -- eapply base_stuck_cas; done.
      * eapply base_stuck_cas_oob; done.
    + eapply base_stuck_cas_no_hdr; done.
  - (* FAA r1 r2 *)
    have [v2 Hv2] : is_Some (to_val r2).
    { destruct (to_val r2) eqn:H; [by eauto|exfalso].
      discriminate (Hredx [CtxFAA2 r1] r2 eq_refl H). }
    apply of_to_val in Hv2; subst r2.
    have [v1 Hv1] : is_Some (to_val r1).
    { destruct (to_val r1) eqn:H; [by eauto|exfalso].
      discriminate (Hredx [CtxFAA1 v2] r1 eq_refl H). }
    apply of_to_val in Hv1; subst r1.
    destruct v1 as [lit|i recs|gen tag vs]; try (eapply base_stuck_faa_bad; [reflexivity|exact I]).
    destruct gen as [bid|]; [eapply base_stuck_faa_bad; [reflexivity|exact I]|].
    destruct tag as [|tag']; [|eapply base_stuck_faa_bad; [reflexivity|exact I]].
    destruct vs as [| [[ba|na|l|]|ia ra|ga ta vsa] [| [[bb|fld|lb|]|ib rb|gb tb vsb] [|c vs']]];
    try (eapply base_stuck_faa_bad; [reflexivity|exact I]).
    destruct v2 as [[bn|n|ln|]|iv rv|gv tv vv];
    try (eapply base_stuck_faa_bad; [reflexivity|exact I]).
    destruct (state_headers σ !! l) as [hdr|] eqn:Hhdr.
    + destruct (decide (0 ≤ fld < header_size hdr)%Z) as [Hbd|Hbd].
      * destruct (state_heap σ !! (l +ₗ fld)) as [w|] eqn:Hcell.
        -- destruct w as [[bw|m|lw|]|iw rw|gw tw vw];
             try (eapply base_stuck_faa_not_int;
                  [reflexivity|exact Hhdr|exact Hbd|exact Hcell|intros mm; discriminate]).
           exfalso. eapply Hstep; [exact (base_step_faa p l fld n m σ Hcell)|unfold wf_access; simpl; exists hdr; done].
        -- eapply base_stuck_faa_no_cell; done.
      * eapply base_stuck_faa_oob; done.
    + eapply base_stuck_faa_no_hdr; done.
  - (* Fork r *)
    exfalso. eapply Hstep; [exact (base_step_fork' p r σ)|unfold wf_access; simpl; exact I].
  - (* GetLocal *)
    destruct (state_locals σ !! p) as [v|] eqn:Hloc.
    + exfalso. eapply Hstep; [exact (base_step_get_local p v σ Hloc)|unfold wf_access; simpl; exact I].
    + eapply base_stuck_get_local; done.
  - (* SetLocal r *)
    have [v Hv0] : is_Some (to_val r).
    { destruct (to_val r) eqn:H; [by eauto|exfalso].
      discriminate (Hredx [CtxSetLocal] r eq_refl H). }
    apply of_to_val in Hv0; subst r.
    destruct (state_locals σ !! p) as [w|] eqn:Hloc.
    + exfalso. eapply Hstep; [apply (base_step_set_local p v σ); rewrite Hloc; by eauto|unfold wf_access; simpl; exact I].
    + eapply base_stuck_set_local; done.
  - (* Emit r: [Emit #v] always steps, so it is never stuck *)
    have [v Hv0] : is_Some (to_val r).
    { destruct (to_val r) eqn:H; [by eauto|exfalso].
      discriminate (Hredx [CtxEmit] r eq_refl H). }
    apply of_to_val in Hv0; subst r.
    exfalso. eapply Hstep; [exact (base_step_emit p v σ)|unfold wf_access; simpl; exact I].
Qed.
