From stdpp Require Import relations.
From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi.lib Require Import fixpoint_mono.

From mizzle.lang Require Import instances.

From mizzle.logic Require Import interp goal adequacy.

(** ψ-translation: every physical location used by the operational state
    has a logical image. The bijection is recorded as a [gmap location
    location] and applied pointwise to locations, literals, expressions,
    values and evaluation contexts. *)

Definition tr_loc (ψ:gmap location location) (l:location) : location :=
  default l (ψ !! l).

Definition tr_inj (ψ:gmap location location) : Prop :=
  ∀ l1 l2 l, ψ !! l1 = Some l → ψ !! l2 = Some l → l1 = l2.

Definition tr_lit ψ (lit:literal) : literal :=
  match lit with
  | LitLoc l => LitLoc (tr_loc ψ l)
  | _ => lit
  end.

Fixpoint tr_expr (ψ:gmap location location) (e:expr) {struct e} : expr :=
  match e with
  | Val v => Val (tr_val ψ v)
  | Var x => Var x
  | Rec f x e => Rec f x (tr_expr ψ e)
  | App e1 e2 => App (tr_expr ψ e1) (tr_expr ψ e2)
  | Let x e1 e2 => Let x (tr_expr ψ e1) (tr_expr ψ e2)
  | Unop op e => Unop op (tr_expr ψ e)
  | Binop op e1 e2 => Binop op (tr_expr ψ e1) (tr_expr ψ e2)
  | Equal e1 e2 => Equal (tr_expr ψ e1) (tr_expr ψ e2)
  | If e0 e1 e2 => If (tr_expr ψ e0) (tr_expr ψ e1) (tr_expr ψ e2)
  | While e0 e1 => While (tr_expr ψ e0) (tr_expr ψ e1)
  | For e1 e2 e3 => For (tr_expr ψ e1) (tr_expr ψ e2) (tr_expr ψ e3)
  | Alloc e1 e2 => Alloc (tr_expr ψ e1) (tr_expr ψ e2)
  | Block mut tag es => Block mut tag (tr_expr ψ <$> es)
  | Match e0 x e1 brs =>
      Match (tr_expr ψ e0) x (tr_expr ψ e1)
        ((λ br, (br.1, tr_expr ψ br.2)) <$> brs)
  | GetTag e => GetTag (tr_expr ψ e)
  | GetSize e => GetSize (tr_expr ψ e)
  | GetField atm e1 e2 => GetField atm (tr_expr ψ e1) (tr_expr ψ e2)
  | SetField atm e1 e2 e3 => SetField atm (tr_expr ψ e1) (tr_expr ψ e2) (tr_expr ψ e3)
  | Xchg e1 e2 => Xchg (tr_expr ψ e1) (tr_expr ψ e2)
  | CAS e0 e1 e2 => CAS (tr_expr ψ e0) (tr_expr ψ e1) (tr_expr ψ e2)
  | FAA e1 e2 => FAA (tr_expr ψ e1) (tr_expr ψ e2)
  | Fork e => Fork (tr_expr ψ e)
  | GetLocal => GetLocal
  | SetLocal e => SetLocal (tr_expr ψ e)
  | Emit e0 => Emit (tr_expr ψ e0)
  end
with tr_val (ψ:gmap location location) (v:val) {struct v} : val :=
  match v with
  | ValLit lit => ValLit (tr_lit ψ lit)
  | ValRecs i recs =>
      ValRecs i ((λ r, (r.1, tr_expr ψ r.2)) <$> recs)
  | ValBlock gen tag vs => ValBlock gen tag (tr_val ψ <$> vs)
  end.

Definition tr_ectxi (ψ:gmap location location) (k:ectxi) : ectxi :=
  match k with
  | CtxApp1 v2 => CtxApp1 (tr_val ψ v2)
  | CtxApp2 e1 => CtxApp2 (tr_expr ψ e1)
  | CtxLet x e2 => CtxLet x (tr_expr ψ e2)
  | CtxUnop op => CtxUnop op
  | CtxBinop1 op v2 => CtxBinop1 op (tr_val ψ v2)
  | CtxBinop2 op e1 => CtxBinop2 op (tr_expr ψ e1)
  | CtxEqual1 v2 => CtxEqual1 (tr_val ψ v2)
  | CtxEqual2 e1 => CtxEqual2 (tr_expr ψ e1)
  | CtxIf e1 e2 => CtxIf (tr_expr ψ e1) (tr_expr ψ e2)
  | CtxFor1 e2 e3 => CtxFor1 (tr_expr ψ e2) (tr_expr ψ e3)
  | CtxFor2 v1 e3 => CtxFor2 (tr_val ψ v1) (tr_expr ψ e3)
  | CtxAlloc1 v2 => CtxAlloc1 (tr_val ψ v2)
  | CtxAlloc2 e1 => CtxAlloc2 (tr_expr ψ e1)
  | CtxBlock mut tag es vs =>
      CtxBlock mut tag (map (tr_expr ψ) es) (map (tr_val ψ) vs)
  | CtxMatch x e1 brs =>
      CtxMatch x (tr_expr ψ e1) (map (λ br, (br.1, tr_expr ψ br.2)) brs)
  | CtxGetTag => CtxGetTag
  | CtxGetSize => CtxGetSize
  | CtxGetField1 atm v2 => CtxGetField1 atm (tr_val ψ v2)
  | CtxGetField2 atm e1 => CtxGetField2 atm (tr_expr ψ e1)
  | CtxSetField1 atm v2 v3 => CtxSetField1 atm (tr_val ψ v2) (tr_val ψ v3)
  | CtxSetField2 atm e1 v3 => CtxSetField2 atm (tr_expr ψ e1) (tr_val ψ v3)
  | CtxSetField3 atm e1 e2 => CtxSetField3 atm (tr_expr ψ e1) (tr_expr ψ e2)
  | CtxXchg1 v2 => CtxXchg1 (tr_val ψ v2)
  | CtxXchg2 e1 => CtxXchg2 (tr_expr ψ e1)
  | CtxCAS0 v1 v2 => CtxCAS0 (tr_val ψ v1) (tr_val ψ v2)
  | CtxCAS1 e0 v2 => CtxCAS1 (tr_expr ψ e0) (tr_val ψ v2)
  | CtxCAS2 e0 e1 => CtxCAS2 (tr_expr ψ e0) (tr_expr ψ e1)
  | CtxFAA1 v2 => CtxFAA1 (tr_val ψ v2)
  | CtxFAA2 e1 => CtxFAA2 (tr_expr ψ e1)
  | CtxSetLocal => CtxSetLocal
  | CtxEmit => CtxEmit
  end.

Definition tr_ectx ψ (K:ectx) : ectx := map (tr_ectxi ψ) K.


Definition locs_lit (lit:literal) : gset location :=
  match lit with
  | LitLoc l => {[l]}
  | _ => ∅
  end.

Fixpoint locs_expr (e:expr) {struct e} : gset location :=
  match e with
  | Val v => locs_val v
  | Var _ => ∅
  | Rec _ _ e => locs_expr e
  | App e1 e2 => locs_expr e1 ∪ locs_expr e2
  | Let _ e1 e2 => locs_expr e1 ∪ locs_expr e2
  | Unop _ e => locs_expr e
  | Binop _ e1 e2 => locs_expr e1 ∪ locs_expr e2
  | Equal e1 e2 => locs_expr e1 ∪ locs_expr e2
  | If e0 e1 e2 => locs_expr e0 ∪ locs_expr e1 ∪ locs_expr e2
  | While e0 e1 => locs_expr e0 ∪ locs_expr e1
  | For e1 e2 e3 => locs_expr e1 ∪ locs_expr e2 ∪ locs_expr e3
  | Alloc e1 e2 => locs_expr e1 ∪ locs_expr e2
  | Block _ _ es => ⋃ (locs_expr <$> es)
  | Match e0 _ e1 brs => locs_expr e0 ∪ locs_expr e1 ∪ ⋃ ((λ br, locs_expr br.2) <$> brs)
  | GetTag e => locs_expr e
  | GetSize e => locs_expr e
  | GetField _ e1 e2 => locs_expr e1 ∪ locs_expr e2
  | SetField _ e1 e2 e3 => locs_expr e1 ∪ locs_expr e2 ∪ locs_expr e3
  | Xchg e1 e2 => locs_expr e1 ∪ locs_expr e2
  | CAS e0 e1 e2 => locs_expr e0 ∪ locs_expr e1 ∪ locs_expr e2
  | FAA e1 e2 => locs_expr e1 ∪ locs_expr e2
  | Fork e => locs_expr e
  | GetLocal => ∅
  | SetLocal e => locs_expr e
  | Emit e0 => locs_expr e0
  end
with locs_val (v:val) {struct v} : gset location :=
  match v with
  | ValLit lit => locs_lit lit
  | ValRecs _ recs => ⋃ ((λ r, locs_expr r.2) <$> recs)
  | ValBlock _ _ vs => ⋃ (locs_val <$> vs)
  end.

(** Well-formedness w.r.t. ψ: every physical location mentioned by the
    expression/value lives in [dom ψ].  Used as an invariant in
    [mirror] so that extending ψ with fresh keys does not change the
    translation of in-flight terms. *)

Definition wf_expr (ψ:gmap location location) (e:expr) : Prop := locs_expr e ⊆ dom ψ.
Definition wf_val  (ψ:gmap location location) (v:val)  : Prop := locs_val  v ⊆ dom ψ.

Lemma locs_val_immediate v : val_immediate v → locs_val v = ∅.
Proof.
  destruct v as [lit| |tag mut vs]; simpl; try done.
  - destruct lit; done.
  - destruct vs; done.
Qed.

(** Location-set lemmas for evaluation contexts and substitution. *)

Definition locs_ectxi (k:ectxi) : gset location :=
  match k with
  | CtxApp1 v2 => locs_val v2
  | CtxApp2 e1 => locs_expr e1
  | CtxLet _ e2 => locs_expr e2
  | CtxUnop _ => ∅
  | CtxBinop1 _ v2 => locs_val v2
  | CtxBinop2 _ e1 => locs_expr e1
  | CtxEqual1 v2 => locs_val v2
  | CtxEqual2 e1 => locs_expr e1
  | CtxIf e1 e2 => locs_expr e1 ∪ locs_expr e2
  | CtxFor1 e2 e3 => locs_expr e2 ∪ locs_expr e3
  | CtxFor2 v1 e3 => locs_val v1 ∪ locs_expr e3
  | CtxAlloc1 v2 => locs_val v2
  | CtxAlloc2 e1 => locs_expr e1
  | CtxBlock _ _ es vs => ⋃ (locs_expr <$> es) ∪ ⋃ (locs_val <$> vs)
  | CtxMatch _ e1 brs => locs_expr e1 ∪ ⋃ ((λ br, locs_expr br.2) <$> brs)
  | CtxGetTag => ∅
  | CtxGetSize => ∅
  | CtxGetField1 _ v2 => locs_val v2
  | CtxGetField2 _ e1 => locs_expr e1
  | CtxSetField1 _ v2 v3 => locs_val v2 ∪ locs_val v3
  | CtxSetField2 _ e1 v3 => locs_expr e1 ∪ locs_val v3
  | CtxSetField3 _ e1 e2 => locs_expr e1 ∪ locs_expr e2
  | CtxXchg1 v2 => locs_val v2
  | CtxXchg2 e1 => locs_expr e1
  | CtxCAS0 v1 v2 => locs_val v1 ∪ locs_val v2
  | CtxCAS1 e0 v2 => locs_expr e0 ∪ locs_val v2
  | CtxCAS2 e0 e1 => locs_expr e0 ∪ locs_expr e1
  | CtxFAA1 v2 => locs_val v2
  | CtxFAA2 e1 => locs_expr e1
  | CtxSetLocal => ∅
  | CtxEmit => ∅
  end.
Definition locs_ectx  (K:ectx)  : gset location := ⋃ (locs_ectxi <$> K).

Lemma locs_of_vals vs : locs_expr <$> of_vals vs = locs_val <$> vs.
Proof.
  rewrite /of_vals -list_fmap_compose. done.
Qed.

Lemma locs_filli k e : locs_expr (filli k e) = locs_ectxi k ∪ locs_expr e.
Proof.
  induction k; simpl; try set_solver.
  rewrite fmap_app /=. rewrite union_list_app_L /=.
  replace (list_fmap expr (gset location) locs_expr) with (fmap (M:=list) locs_expr) by reflexivity.
  rewrite locs_of_vals. set_solver.
Qed.

Lemma locs_fill K e : locs_expr (fill K e) = locs_ectx K ∪ locs_expr e.
Proof.
  revert e. induction K as [|k K IH]; intros e.
  - simpl. rewrite /locs_ectx /=. set_solver.
  - simpl. rewrite IH locs_filli /locs_ectx /=. set_solver.
Qed.

Lemma locs_subst x v e : locs_expr (subst x v e) ⊆ locs_val v ∪ locs_expr e.
Proof.
  revert e.
  refine (expr_val_ind
    (fun e => locs_expr (subst x v e) ⊆ locs_val v ∪ locs_expr e)
    (fun _ => True)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  - (* Val *) intros vv _. simpl. set_solver.
  - (* Var *) intros y. simpl. case_match; simpl; set_solver.
  - (* Rec *) intros f y e IH. simpl. case_match; simpl; set_solver.
  - (* App *) intros e1 IH1 e2 IH2. simpl. set_solver.
  - (* Let *) intros y e1 e2 IH1 IH2. simpl. case_match; simpl; set_solver.
  - (* Unop *) intros op e IH. simpl. set_solver.
  - (* Binop *) intros op e1 IH1 e2 IH2. simpl. set_solver.
  - (* Equal *) intros e1 IH1 e2 IH2. simpl. set_solver.
  - (* If *) intros e0 IH0 e1 IH1 e2 IH2. simpl. set_solver.
  - (* While *) intros e0 IH0 e1 IH1. simpl. set_solver.
  - (* For *) intros e1 IH1 e2 IH2 e3 IH3. simpl. set_solver.
  - (* Alloc *) intros e1 IH1 e2 IH2. simpl. set_solver.
  - (* Block *) intros mut tag es Hes. simpl. intros k Hk.
    apply elem_of_union_list in Hk as [s [Hsfmap Hin]].
    apply list_elem_of_fmap in Hsfmap as (esubst & -> & Hes2).
    apply list_elem_of_fmap in Hes2 as (e0 & -> & (i & He0)%list_elem_of_lookup).
    pose proof (Forall_lookup_1 _ _ _ _ Hes He0) as Hsub. simpl in Hsub.
    assert (locs_expr e0 ⊆ ⋃ (locs_expr <$> es)) as Hsub2.
    { intros y Hy. apply elem_of_union_list. exists (locs_expr e0). split; last done.
      apply list_elem_of_fmap. exists e0. split; first done.
      eapply list_elem_of_lookup_2; eassumption. }
    set_solver.
  - (* Match *) intros e0 IH0 y e1 IH1 brs Hbrs. simpl. intros k Hk.
    apply elem_of_union in Hk as Hcase. destruct Hcase as [Hk1|Hk2].
    + apply elem_of_union in Hk1 as Hc. destruct Hc as [Hk1'|Hk1'].
      * specialize (IH0 _ Hk1'). set_solver.
      * destruct (_ ≟ _); first set_solver. specialize (IH1 _ Hk1'). set_solver.
    + apply elem_of_union_list in Hk2 as [s [Hsfmap Hin]].
      apply list_elem_of_fmap in Hsfmap as (br' & -> & Hbr').
      apply list_elem_of_fmap in Hbr' as (br & Hbreq & (i & Hbri)%list_elem_of_lookup).
      subst br'. simpl in Hin.
      assert (locs_expr br.2 ⊆ ⋃ ((λ br0 : branch, locs_expr br0.2) <$> brs)) as Hsub2.
      { intros y' Hy'. apply elem_of_union_list. exists (locs_expr br.2). split; last done.
        apply list_elem_of_fmap. exists br. split; first done.
        eapply list_elem_of_lookup_2; eassumption. }
      destruct (_ || _); first set_solver.
      pose proof (Forall_lookup_1 _ _ _ _ Hbrs Hbri) as Hsub. simpl in Hsub.
      set_solver.
  - (* GetTag *) intros e IH. simpl. set_solver.
  - (* GetSize *) intros e IH. simpl. set_solver.
  - (* GetField *) intros atm e1 IH1 e2 IH2. simpl. set_solver.
  - (* SetField *) intros atm e1 IH1 e2 IH2 e3 IH3. simpl. set_solver.
  - (* Xchg *) intros e1 IH1 e2 IH2. simpl. set_solver.
  - (* CAS *) intros e0 IH0 e1 IH1 e2 IH2. simpl. set_solver.
  - (* FAA *) intros e1 IH1 e2 IH2. simpl. set_solver.
  - (* Fork *) intros e IH. simpl. set_solver.
  - (* GetLocal *) simpl. set_solver.
  - (* SetLocal *) intros e IH. simpl. set_solver.
  - (* Emit *) intros e0 IH0. simpl. set_solver.
  - (* ValLit *) done.
  - (* ValRecs *) done.
  - (* ValBlock *) done.
Qed.

Lemma locs_subst' x v e : locs_expr (subst' x v e) ⊆ locs_val v ∪ locs_expr e.
Proof. destruct x; simpl; [set_solver|apply locs_subst]. Qed.

Lemma locs_eval_unop op v v' :
  eval_unop op v = Some v' → locs_val v' = ∅.
Proof.
  destruct op, v as [lit|? ?|? ? ?]; simpl; try done;
    try (destruct lit; try done); intros [= <-]; done.
Qed.

Lemma locs_eval_binop op v1 v2 v' :
  eval_binop op v1 v2 = Some v' → locs_val v' = ∅.
Proof.
  destruct v1 as [lit1|? ?|? ? ?], v2 as [lit2|? ?|? ? ?]; simpl; try done.
  all: destruct lit1; try done.
  all: try (destruct lit2; try done; intros [= <-]; cbn; destruct op; done).
Qed.

Definition locs_subj (subj:subject) : gset location :=
  match subj with
  | SubjectLoc l => {[l]}
  | SubjectBlock _ vs => ⋃ (locs_val <$> vs)
  end.

Lemma locs_subject_to_val tag subj : locs_val (subject_to_val tag subj) = locs_subj subj.
Proof. destruct subj; reflexivity. Qed.

Lemma locs_subst_list xs vs e :
  locs_expr (subst_list xs vs e) ⊆ ⋃ (locs_val <$> vs) ∪ locs_expr e.
Proof.
  revert vs e. induction xs as [|x xs IH]; intros [|v vs] e; simpl; try set_solver.
  pose proof (locs_subst' x v (subst_list xs vs e)).
  specialize (IH vs e). set_solver.
Qed.

Lemma locs_eval_match tag sz subj x_fb e_fb brs e' :
  eval_match tag sz subj x_fb e_fb brs = Some e' →
  locs_expr e' ⊆ locs_subj subj ∪ locs_expr e_fb ∪ ⋃ ((λ br, locs_expr br.2) <$> brs).
Proof.
  revert e'. induction brs as [|br brs IH]; intros e' Heq.
  - simpl in Heq. injection Heq as <-. simpl.
    pose proof (locs_subst' x_fb (subject_to_val tag subj) e_fb) as Hs.
    rewrite locs_subject_to_val in Hs. set_solver.
  - cbn in Heq. unfold eval_match in Heq. case_match.
    2:{ specialize (IH _ Heq). simpl. set_solver. }
    destruct subj as [l|gen vs].
    + destruct (forallb _ _) eqn:Ef; last done. injection Heq as <-.
      pose proof (locs_subst' br.1.(pattern_as) (ValLoc l) br.2) as Hs.
      simpl in Hs |- *. set_solver.
    + injection Heq as <-.
      pose proof (locs_subst_list br.1.(pattern_fields) vs
                    (subst' br.1.(pattern_as) (ValBlock gen tag vs) br.2)) as Hsl.
      pose proof (locs_subst' br.1.(pattern_as) (ValBlock gen tag vs) br.2) as Hs.
      simpl in Hs |- *. set_solver.
Qed.

Lemma wf_fill ψ K e : wf_expr ψ (fill K e) ↔ locs_ectx K ⊆ dom ψ ∧ wf_expr ψ e.
Proof. rewrite /wf_expr locs_fill union_subseteq //. Qed.

Lemma wf_fill_mono ψ K e1 e2 :
  locs_expr e2 ⊆ locs_expr e1 →
  wf_expr ψ (fill K e1) → wf_expr ψ (fill K e2).
Proof. rewrite !wf_fill /wf_expr. set_solver. Qed.

(** Monotonicity of [wf_*] in ψ: extending ψ keeps everything wf. *)
Lemma wf_val_mono ψ ψ' v : dom ψ ⊆ dom ψ' → wf_val ψ v → wf_val ψ' v.
Proof. rewrite /wf_val. set_solver. Qed.
Lemma wf_expr_mono ψ ψ' e : dom ψ ⊆ dom ψ' → wf_expr ψ e → wf_expr ψ' e.
Proof. rewrite /wf_expr. set_solver. Qed.

(** [tr_loc] is stable when ψ' agrees with ψ on [dom ψ] and [l ∈ dom ψ]. *)
Lemma tr_loc_agree ψ ψ' l :
  (∀ k, k ∈ dom ψ → ψ' !! k = ψ !! k) →
  l ∈ dom ψ → tr_loc ψ' l = tr_loc ψ l.
Proof. intros Hagree Hin. rewrite /tr_loc Hagree //. Qed.

(** [tr_val] / [tr_expr] are stable under any ψ → ψ' such that ψ' agrees
    with ψ on the locations occurring in the term. *)
Lemma tr_expr_val_agree ψ ψ' :
  (∀ e, (∀ k, k ∈ locs_expr e → ψ' !! k = ψ !! k) → tr_expr ψ' e = tr_expr ψ e) ∧
  (∀ v, (∀ k, k ∈ locs_val v → ψ' !! k = ψ !! k) → tr_val ψ' v = tr_val ψ v).
Proof.
  apply expr_val_mutind.
  - (* Val *) intros v IHv Hag. simpl. f_equal. by apply IHv.
  - (* Var *) done.
  - (* Rec *) intros f x e IHe Hag. simpl. f_equal. by apply IHe.
  - (* App *) intros e1 IH1 e2 IH2 Hag. simpl. f_equal; [apply IH1|apply IH2]; set_solver.
  - (* Let *) intros x e1 IH1 e2 IH2 Hag. simpl. f_equal; [apply IH1|apply IH2]; set_solver.
  - (* Unop *) intros op e IH Hag. simpl. f_equal. by apply IH.
  - (* Binop *) intros op e1 IH1 e2 IH2 Hag. simpl. f_equal; [apply IH1|apply IH2]; set_solver.
  - (* Equal *) intros e1 IH1 e2 IH2 Hag. simpl. f_equal; [apply IH1|apply IH2]; set_solver.
  - (* If *) intros e0 IH0 e1 IH1 e2 IH2 Hag. simpl. f_equal; [apply IH0|apply IH1|apply IH2]; set_solver.
  - (* While *) intros e0 IH0 e1 IH1 Hag. simpl. f_equal; [apply IH0|apply IH1]; set_solver.
  - (* For *) intros e1 IH1 e2 IH2 e3 IH3 Hag. simpl. f_equal; [apply IH1|apply IH2|apply IH3]; set_solver.
  - (* Alloc *) intros e1 IH1 e2 IH2 Hag. simpl. f_equal; [apply IH1|apply IH2]; set_solver.
  - (* Block *) intros mut tag es IHes Hag. simpl. f_equal. apply list_fmap_ext.
    intros j e Hj. apply (Forall_lookup_1 _ _ _ _ IHes Hj). intros k Hk. apply Hag. simpl.
    apply elem_of_union_list. exists (locs_expr e). split; last done.
    apply list_elem_of_fmap. exists e. split; first done. eapply list_elem_of_lookup_2; eassumption.
  - (* Match *) intros e0 IH0 x e1 IH1 brs IHbrs Hag. simpl. f_equal.
    + apply IH0. set_solver.
    + apply IH1. set_solver.
    + apply list_fmap_ext. intros j [b e] Hj. f_equal. simpl.
      apply (Forall_lookup_1 _ _ _ _ IHbrs Hj). intros k Hk. apply Hag. simpl.
      apply elem_of_union_r.
      apply elem_of_union_list. exists (locs_expr e). split; last done.
      apply list_elem_of_fmap. exists (b, e). split; first done. eapply list_elem_of_lookup_2; eassumption.
  - (* GetTag *) intros e IH Hag. simpl. f_equal. by apply IH.
  - (* GetSize *) intros e IH Hag. simpl. f_equal. by apply IH.
  - (* GetField *) intros atm e1 IH1 e2 IH2 Hag. simpl. f_equal; [apply IH1|apply IH2]; set_solver.
  - (* SetField *) intros atm e1 IH1 e2 IH2 e3 IH3 Hag. simpl. f_equal; [apply IH1|apply IH2|apply IH3]; set_solver.
  - (* Xchg *) intros e1 IH1 e2 IH2 Hag. simpl. f_equal; [apply IH1|apply IH2]; set_solver.
  - (* CAS *) intros e0 IH0 e1 IH1 e2 IH2 Hag. simpl. f_equal; [apply IH0|apply IH1|apply IH2]; set_solver.
  - (* FAA *) intros e1 IH1 e2 IH2 Hag. simpl. f_equal; [apply IH1|apply IH2]; set_solver.
  - (* Fork *) intros e IH Hag. simpl. f_equal. by apply IH.
  - (* GetLocal *) done.
  - (* SetLocal *) intros e IH Hag. simpl. f_equal. by apply IH.
  - (* Emit *) intros e0 IH0 Hag. simpl. f_equal. apply IH0. set_solver.
  - (* ValLit *) intros lit Hag. simpl. destruct lit; try done. simpl. rewrite /tr_loc Hag //. simpl. set_solver.
  - (* ValRecs *) intros i recs IHrecs Hag. simpl. f_equal. apply list_fmap_ext.
    intros j [b e] Hj. f_equal. simpl. apply (Forall_lookup_1 _ _ _ _ IHrecs Hj). intros k Hk.
    apply Hag. simpl. apply elem_of_union_list. exists (locs_expr e). split; last done.
    apply list_elem_of_fmap. exists (b, e). split; first done. eapply list_elem_of_lookup_2; eassumption.
  - (* ValBlock *) intros gen tag vs IHvs Hag. simpl. f_equal. apply list_fmap_ext.
    intros j v Hj. apply (Forall_lookup_1 _ _ _ _ IHvs Hj). intros k Hk.
    apply Hag. simpl. apply elem_of_union_list. exists (locs_val v). split; last done.
    apply list_elem_of_fmap. exists v. split; first done. eapply list_elem_of_lookup_2; eassumption.
Qed.

Lemma tr_expr_agree ψ ψ' e :
  (∀ k, k ∈ locs_expr e → ψ' !! k = ψ !! k) →
  tr_expr ψ' e = tr_expr ψ e.
Proof. apply tr_expr_val_agree. Qed.

Lemma tr_val_agree ψ ψ' v :
  (∀ k, k ∈ locs_val v → ψ' !! k = ψ !! k) →
  tr_val ψ' v = tr_val ψ v.
Proof. apply tr_expr_val_agree. Qed.

Lemma tr_val_extend ψ ψ' v :
  (∀ k, k ∈ dom ψ → ψ' !! k = ψ !! k) →
  wf_val ψ v → tr_val ψ' v = tr_val ψ v.
Proof. intros Hagree Hwf. apply tr_val_agree. intros k Hk. apply Hagree, Hwf, Hk. Qed.

Lemma tr_expr_extend ψ ψ' e :
  (∀ k, k ∈ dom ψ → ψ' !! k = ψ !! k) →
  wf_expr ψ e → tr_expr ψ' e = tr_expr ψ e.
Proof. intros Hagree Hwf. apply tr_expr_agree. intros k Hk. apply Hagree, Hwf, Hk. Qed.

(** If [e] mentions no location of [dom ψ], then [tr_expr ψ] acts as the
    identity on [e].  Same for values. *)
Lemma tr_expr_val_locs_out :
  (∀ e ψ, locs_expr e ## dom ψ → tr_expr ψ e = e) ∧
  (∀ v ψ, locs_val  v ## dom ψ → tr_val  ψ v = v).
Proof.
  apply expr_val_mutind.
  - (* Val *) intros v IHv ψ Hd. simpl. f_equal. by apply IHv.
  - (* Var *) done.
  - (* Rec *) intros f x e IHe ψ Hd. simpl. f_equal. by apply IHe.
  - (* App *) intros e1 IH1 e2 IH2 ψ Hd. simpl. f_equal; [apply IH1|apply IH2]; set_solver.
  - (* Let *) intros x e1 IH1 e2 IH2 ψ Hd. simpl. f_equal; [apply IH1|apply IH2]; set_solver.
  - (* Unop *) intros op e IH ψ Hd. simpl. f_equal. by apply IH.
  - (* Binop *) intros op e1 IH1 e2 IH2 ψ Hd. simpl. f_equal; [apply IH1|apply IH2]; set_solver.
  - (* Equal *) intros e1 IH1 e2 IH2 ψ Hd. simpl. f_equal; [apply IH1|apply IH2]; set_solver.
  - (* If *) intros e0 IH0 e1 IH1 e2 IH2 ψ Hd. simpl. f_equal; [apply IH0|apply IH1|apply IH2]; set_solver.
  - (* While *) intros e0 IH0 e1 IH1 ψ Hd. simpl. f_equal; [apply IH0|apply IH1]; set_solver.
  - (* For *) intros e1 IH1 e2 IH2 e3 IH3 ψ Hd. simpl. f_equal; [apply IH1|apply IH2|apply IH3]; set_solver.
  - (* Alloc *) intros e1 IH1 e2 IH2 ψ Hd. simpl. f_equal; [apply IH1|apply IH2]; set_solver.
  - (* Block *) intros mut tag es IHes ψ Hd. simpl. f_equal.
    rewrite -{2}(list_fmap_id es). apply list_fmap_ext. intros j e Hj.
    apply (Forall_lookup_1 _ _ _ _ IHes Hj). simpl in Hd.
    apply elem_of_disjoint. intros k Hk Hk'. apply elem_of_disjoint in Hd. apply (Hd k); last done.
    apply elem_of_union_list. exists (locs_expr e). split; last done.
    apply list_elem_of_fmap. exists e. split; first done. eapply list_elem_of_lookup_2; eassumption.
  - (* Match *) intros e0 IH0 x e1 IH1 brs IHbrs ψ Hd. simpl. f_equal.
    + apply IH0. set_solver.
    + apply IH1. set_solver.
    + rewrite -{2}(list_fmap_id brs). apply list_fmap_ext. intros j [b e] Hj.
      simpl. f_equal. apply (Forall_lookup_1 _ _ _ _ IHbrs Hj). simpl in Hd.
      apply elem_of_disjoint. intros k Hk Hk'. apply elem_of_disjoint in Hd. apply (Hd k); last done.
      apply elem_of_union_r, elem_of_union_list.
      exists (locs_expr e). split; last done.
      apply list_elem_of_fmap. exists (b, e). split; first done. eapply list_elem_of_lookup_2; eassumption.
  - (* GetTag *) intros e IH ψ Hd. simpl. f_equal. by apply IH.
  - (* GetSize *) intros e IH ψ Hd. simpl. f_equal. by apply IH.
  - (* GetField *) intros atm e1 IH1 e2 IH2 ψ Hd. simpl. f_equal; [apply IH1|apply IH2]; set_solver.
  - (* SetField *) intros atm e1 IH1 e2 IH2 e3 IH3 ψ Hd. simpl. f_equal; [apply IH1|apply IH2|apply IH3]; set_solver.
  - (* Xchg *) intros e1 IH1 e2 IH2 ψ Hd. simpl. f_equal; [apply IH1|apply IH2]; set_solver.
  - (* CAS *) intros e0 IH0 e1 IH1 e2 IH2 ψ Hd. simpl. f_equal; [apply IH0|apply IH1|apply IH2]; set_solver.
  - (* FAA *) intros e1 IH1 e2 IH2 ψ Hd. simpl. f_equal; [apply IH1|apply IH2]; set_solver.
  - (* Fork *) intros e IH ψ Hd. simpl. f_equal. by apply IH.
  - (* GetLocal *) done.
  - (* SetLocal *) intros e IH ψ Hd. simpl. f_equal. by apply IH.
  - (* Emit *) intros e0 IH0 ψ Hd. simpl. f_equal. apply IH0. set_solver.
  - (* ValLit *) intros lit ψ Hd. simpl. destruct lit; try done. simpl.
    rewrite /tr_loc. rewrite (_ : ψ !! l = None) //.
    apply not_elem_of_dom. simpl in Hd. set_solver.
  - (* ValRecs *) intros i recs IHrecs ψ Hd. simpl. f_equal.
    rewrite -{2}(list_fmap_id recs). apply list_fmap_ext. intros j [b e] Hj.
    simpl. f_equal. apply (Forall_lookup_1 _ _ _ _ IHrecs Hj). simpl in Hd.
    apply elem_of_disjoint. intros k Hk Hk'. apply elem_of_disjoint in Hd. apply (Hd k); last done.
    apply elem_of_union_list. exists (locs_expr e). split; last done.
    apply list_elem_of_fmap. exists (b, e). split; first done. eapply list_elem_of_lookup_2; eassumption.
  - (* ValBlock *) intros gen tag vs IHvs ψ Hd. simpl. f_equal.
    rewrite -{2}(list_fmap_id vs). apply list_fmap_ext. intros j v Hj.
    apply (Forall_lookup_1 _ _ _ _ IHvs Hj). simpl in Hd.
    apply elem_of_disjoint. intros k Hk Hk'. apply elem_of_disjoint in Hd. apply (Hd k); last done.
    apply elem_of_union_list. exists (locs_val v). split; last done.
    apply list_elem_of_fmap. exists v. split; first done. eapply list_elem_of_lookup_2; eassumption.
Qed.

Lemma tr_locs_out ψ e :
  locs_expr e ## dom ψ → tr_expr ψ e = e.
Proof. apply tr_expr_val_locs_out. Qed.

Lemma tr_ectxi_extend ψ ψ' k :
  (∀ k0, k0 ∈ dom ψ → ψ' !! k0 = ψ !! k0) →
  locs_ectxi k ⊆ dom ψ → tr_ectxi ψ' k = tr_ectxi ψ k.
Proof.
  intros Hagree Hwf.
  induction k; simpl in Hwf |- *; try done.
  all: f_equal; try (apply tr_val_agree; intros ? ?; apply Hagree; set_solver);
    try (apply tr_expr_agree; intros ? ?; apply Hagree; set_solver).
  - (* Block es *) apply list_fmap_ext. intros j e Hj. apply tr_expr_agree.
    intros k Hk. apply Hagree, Hwf. apply elem_of_union_l.
    apply elem_of_union_list. exists (locs_expr e). split; last done.
    apply list_elem_of_fmap. exists e. split; first done. eapply list_elem_of_lookup_2; eassumption.
  - (* Block vs *) apply list_fmap_ext. intros j v Hj. apply tr_val_agree.
    intros k Hk. apply Hagree, Hwf. apply elem_of_union_r.
    apply elem_of_union_list. exists (locs_val v). split; last done.
    apply list_elem_of_fmap. exists v. split; first done. eapply list_elem_of_lookup_2; eassumption.
  - (* Match brs *) apply list_fmap_ext. intros j [b e] Hj. f_equal. simpl. apply tr_expr_agree.
    intros k Hk. apply Hagree, Hwf. apply elem_of_union_r.
    apply elem_of_union_list. exists (locs_expr e). split; last done.
    apply list_elem_of_fmap. exists (b, e). split; first done. eapply list_elem_of_lookup_2; eassumption.
Qed.

Lemma tr_ectx_extend ψ ψ' K :
  (∀ k, k ∈ dom ψ → ψ' !! k = ψ !! k) →
  locs_ectx K ⊆ dom ψ → tr_ectx ψ' K = tr_ectx ψ K.
Proof.
  intros Hagree. induction K as [|k K IH]; first done. intros HK.
  rewrite /tr_ectx /=. f_equal.
  - apply tr_ectxi_extend; first done.
    rewrite /locs_ectx /= in HK. set_solver.
  - apply IH. rewrite /locs_ectx /= in HK. set_solver.
Qed.

Lemma tr_loc_inj_on_dom ψ (Htr : tr_inj ψ) l1 l2 :
  l1 ∈ dom ψ → l2 ∈ dom ψ → tr_loc ψ l1 = tr_loc ψ l2 → l1 = l2.
Proof.
  rewrite /tr_loc !elem_of_dom.
  intros [v1 H1] [v2 H2] Heq.
  rewrite H1 H2 /= in Heq. subst v2.
  by apply (Htr _ _ _ H1) in H2 as ->.
Qed.

Lemma tr_of_vals ψ vs :
  of_vals (tr_val ψ <$> vs) = tr_expr ψ <$> of_vals vs.
Proof.
  rewrite /of_vals -list_fmap_compose -list_fmap_compose //.
Qed.

Lemma tr_filli ψ k e :
  tr_expr ψ (filli k e) = filli (tr_ectxi ψ k) (tr_expr ψ e).
Proof.
  revert e. destruct k; intros e; simpl; try done.
  - rewrite fmap_app /=. f_equal. f_equal. by rewrite tr_of_vals.
Qed.

Lemma tr_fill ψ K e :
  tr_expr ψ (fill K e) = fill (tr_ectx ψ K) (tr_expr ψ e).
Proof.
  revert e. induction K as [|k K IH]; intros e; first done.
  simpl. rewrite IH tr_filli //.
Qed.

(* Structural lemmas about [tr_expr] / [tr_val], by mutual induction over
   expr/val; lengthy because of the many AST constructors. *)

Lemma tr_subst ψ y v e :
  tr_expr ψ (subst y v e) = subst y (tr_val ψ v) (tr_expr ψ e).
Proof.
  revert e.
  refine (expr_val_ind
    (fun e => tr_expr ψ (subst y v e) = subst y (tr_val ψ v) (tr_expr ψ e))
    (fun _ => True)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  all: try (intros; simpl; try done; congruence).
  { intros x. simpl. destruct (beq y x); done. }
  { intros f x e IH. simpl.
    destruct (beq (BNamed y) f); simpl; first done.
    destruct (beq (BNamed y) x); simpl; first done.
    by rewrite IH. }
  { intros x e1 IH1 e2 IH2. simpl. rewrite IH1.
    destruct (beq (BNamed y) x); simpl; first done.
    by rewrite IH2. }
  { intros mut tag es Hes. simpl. f_equal.
    rewrite -list_fmap_compose -list_fmap_compose.
    apply list_fmap_ext. intros i x Hx.
    apply (Forall_lookup_1 _ _ _ _ Hes Hx). }
  { intros e0 IH0 x e1 IH1 brs Hbrs. simpl. rewrite IH0. f_equal.
    - destruct (beq (BNamed y) x); simpl; first done. by rewrite IH1.
    - rewrite -!list_fmap_compose. apply list_fmap_ext.
      intros i br Hbr. simpl. f_equal.
      destruct (existsb _ _ || beq (BNamed y) _); simpl; first done.
      apply (Forall_lookup_1 _ _ _ _ Hbrs Hbr). }
Qed.

Lemma tr_subst' ψ y v e :
  tr_expr ψ (subst' y v e) = subst' y (tr_val ψ v) (tr_expr ψ e).
Proof. destruct y; simpl; [done|apply tr_subst]. Qed.

Lemma tr_eval_unop ψ op v v' :
  eval_unop op v = Some v' → eval_unop op (tr_val ψ v) = Some (tr_val ψ v').
Proof.
  destruct op, v; cbn; try done.
  - destruct lit; try done. intros [= <-]. done.
  - destruct lit; try done. intros [= <-]. done.
  - intros [= <-]. cbn. destruct lit; done.
  - intros [= <-]. cbn. done.
  - intros [= <-]. cbn. by destruct vs.
Qed.

Lemma tr_eval_unop_none ψ op v :
  eval_unop op v = None → eval_unop op (tr_val ψ v) = None.
Proof. destruct op, v; cbn; try done; destruct lit; done. Qed.

Lemma tr_eval_binop ψ op v1 v2 v' :
  eval_binop op v1 v2 = Some v' →
  eval_binop op (tr_val ψ v1) (tr_val ψ v2) = Some (tr_val ψ v').
Proof.
  destruct v1 as [lit1|? ?|? ? ?], v2 as [lit2|? ?|? ? ?]; cbn; try done.
  - destruct lit1, lit2; try done.
    intros [= <-]. cbn. f_equal. f_equal. by destruct op.
  - destruct lit1; done.
  - destruct lit1; done.
Qed.

Lemma tr_eval_binop_none ψ op v1 v2 :
  eval_binop op v1 v2 = None → eval_binop op (tr_val ψ v1) (tr_val ψ v2) = None.
Proof.
  destruct v1 as [lit1|? ?|? ? ?], v2 as [lit2|? ?|? ? ?]; cbn; try done;
  destruct lit1; try done; destruct lit2; done.
Qed.

Lemma tr_val_similar ψ v1 v2 :
  v1 ≈ v2 → tr_val ψ v1 ≈ tr_val ψ v2.
Proof.
  rewrite /similar /val_similar.
  revert v2.
  induction v1 as [lit1 | i1 recs1 | gen1 tag1 vs1 IHvs] using val_ind;
    intros [lit2 | i2 recs2 | gen2 tag2 vs2] Hsim; cbn in Hsim |- *.
  - destruct lit1, lit2; cbn in Hsim |- *; inversion Hsim; subst; cbn; reflexivity.
  - destruct lit1; cbn in Hsim; done.
  - destruct vs2 as [|v2' vs2']; cbn in Hsim |- *; last done.
    destruct lit1; cbn in Hsim |- *; inversion Hsim; subst; cbn; reflexivity.
  - destruct lit2; cbn in Hsim; done.
  - done.
  - destruct vs2; cbn in Hsim; done.
  - destruct vs1 as [|v1' vs1']; cbn in Hsim |- *; last done.
    destruct lit2; cbn in Hsim |- *; inversion Hsim; subst; cbn; reflexivity.
  - destruct vs1; cbn in Hsim; done.
  - destruct vs1 as [|v1' vs1'], vs2 as [|v2' vs2']; cbn in Hsim |- *.
    + inversion Hsim; subst; cbn; reflexivity.
    + done.
    + done.
    + destruct gen1 as [bid1|], gen2 as [bid2|]; try done.
      * cbn in Hsim |- *. destruct Hsim as (-> & -> & [= -> ->]). done.
      * cbn in Hsim |- *. destruct Hsim as [-> Hsims].
        split; first reflexivity.
        cbn in Hsims |- *.
        destruct Hsims as [Hh Ht].
        apply Forall_cons in IHvs as [Hx Hxs].
        split.
        { exact (Hx _ Hh). }
        clear Hx Hh.
        revert vs2' Ht.
        induction Hxs as [|v vs HIH Hforall IHls]; intros [|v2 vs2] Ht; cbn in Ht |- *; try done.
        destruct Ht as [Hh Ht].
        split.
        { exact (HIH _ Hh). }
        apply IHls, Ht.
Qed.

Lemma tr_lit_inj ψ (Htr : tr_inj ψ) lit1 lit2 :
  locs_lit lit1 ⊆ dom ψ → locs_lit lit2 ⊆ dom ψ →
  tr_lit ψ lit1 = tr_lit ψ lit2 → lit1 = lit2.
Proof.
  destruct lit1, lit2; cbn; intros Hd1 Hd2; intros [=]; subst; try done.
  f_equal. apply (tr_loc_inj_on_dom _ Htr); [set_solver..|done].
Qed.

Lemma tr_expr_val_inj ψ (Htr : tr_inj ψ) :
  (∀ e1 e2, locs_expr e1 ⊆ dom ψ → locs_expr e2 ⊆ dom ψ →
            tr_expr ψ e1 = tr_expr ψ e2 → e1 = e2) ∧
  (∀ v1 v2, locs_val v1 ⊆ dom ψ → locs_val v2 ⊆ dom ψ →
            tr_val ψ v1 = tr_val ψ v2 → v1 = v2).
Proof.
  apply (expr_val_mutind
    (λ e1, ∀ e2, locs_expr e1 ⊆ dom ψ → locs_expr e2 ⊆ dom ψ →
                 tr_expr ψ e1 = tr_expr ψ e2 → e1 = e2)
    (λ v1, ∀ v2, locs_val v1 ⊆ dom ψ → locs_val v2 ⊆ dom ψ →
                 tr_val ψ v1 = tr_val ψ v2 → v1 = v2)).
  all: try (intros;
    match goal with
    | H : tr_expr _ _ = tr_expr _ ?e |- _ => destruct e
    | H : tr_val _ _ = tr_val _ ?v |- _ => destruct v
    end;
    cbn in *; try discriminate; try done;
    repeat match goal with
    | H : _ = _ |- _ => injection H; clear H; intros
    end;
    subst; f_equal;
    match goal with
    | H : ∀ _ : expr, _ |- ?e = _ => eapply H; eauto; set_solver
    | H : ∀ _ : val, _ |- ?v = _ => eapply H; eauto; set_solver
    end).
  - (* Block *)
    intros mut0 tag0 es Hes e2 Hd1 Hd2 Heq.
    destruct e2; cbn in *; try done.
    injection Heq as -> -> Heq.
    f_equal.
    revert es0 Hd2 Heq. induction Hes as [|e es' Hh Hf IH]; intros [|e0' es0'] Hd2 Heq;
      cbn in *; try done.
    injection Heq as Hh' Ht'. f_equal.
    + apply Hh; [set_solver..|done].
    + apply IH; [set_solver..|done].
  - (* Match *)
    intros e0 He0 x0 e1 He1 brs Hbrs e2 Hd1 Hd2 Heq.
    destruct e2; cbn in *; try done.
    injection Heq as Heq0 -> Heq1 Heqbrs.
    assert (e0 = e2_1) as -> by (apply He0; [set_solver..|done]).
    assert (e1 = e2_2) as -> by (apply He1; [set_solver..|done]).
    f_equal.
    revert brs0 Hd2 Heqbrs. induction Hbrs as [|br brs' Hh Hf IH];
      intros [|br0' brs0'] Hd2 Heqbrs; cbn in *; try done.
    destruct br as [a b], br0' as [c d]. cbn in *.
    inversion Heqbrs as [[Hac Hbd Hrest]]. subst.
    assert (b = d) as -> by (apply Hh; [set_solver..|done]).
    f_equal. apply IH; [set_solver..|done].
  - (* ValLit *)
    intros lit v2 Hd1 Hd2 Heq.
    destruct v2; cbn in *; try done.
    injection Heq as Heq.
    f_equal. apply (tr_lit_inj _ Htr); done.
  - (* ValRecs *)
    intros i0 recs Hrecs v2 Hd1 Hd2 Heq.
    destruct v2; cbn in *; try done.
    injection Heq as -> Heqrecs.
    f_equal.
    revert recs0 Hd2 Heqrecs. induction Hrecs as [|r recs' Hh Hf IH];
      intros [|r0' recs0'] Hd2 Heqrecs; cbn in *; try done.
    destruct r as [a b], r0' as [c d]. cbn in *.
    inversion Heqrecs as [[Hac Hbd Hrest]]. subst.
    assert (b = d) as -> by (apply Hh; [set_solver..|done]).
    f_equal. apply IH; [set_solver..|done].
  - (* ValBlock *)
    intros gen0 tag0 vs Hvs v2 Hd1 Hd2 Heq.
    destruct v2; cbn in *; try done.
    injection Heq as -> -> Heqvs.
    f_equal.
    revert vs0 Hd2 Heqvs. induction Hvs as [|v vs' Hh Hf IH];
      intros [|v0' vs0'] Hd2 Heqvs; cbn in *; try done.
    injection Heqvs as Hh' Ht'. f_equal.
    + apply Hh; [set_solver..|done].
    + apply IH; [set_solver..|done].
Qed.

Lemma tr_val_inj ψ (Htr : tr_inj ψ) v1 v2 :
  locs_val v1 ⊆ dom ψ → locs_val v2 ⊆ dom ψ →
  tr_val ψ v1 = tr_val ψ v2 → v1 = v2.
Proof. apply tr_expr_val_inj, Htr. Qed.

Lemma tr_val_list_inj ψ (Htr : tr_inj ψ) vs1 vs2 :
  ⋃ (locs_val <$> vs1) ⊆ dom ψ →
  ⋃ (locs_val <$> vs2) ⊆ dom ψ →
  tr_val ψ <$> vs1 = tr_val ψ <$> vs2 → vs1 = vs2.
Proof.
  revert vs2. induction vs1 as [|v vs1' IH]; intros [|v' vs2'] Hd1 Hd2 Heq;
    cbn in *; try done.
  injection Heq as Hh Ht. f_equal.
  - apply (tr_val_inj _ Htr); [set_solver..|done].
  - apply IH; [set_solver..|done].
Qed.

Lemma tr_val_nonsimilar ψ (Htr : tr_inj ψ) v1 v2 :
  locs_val v1 ⊆ dom ψ → locs_val v2 ⊆ dom ψ →
  v1 ≉ v2 → tr_val ψ v1 ≉ tr_val ψ v2.
Proof.
  intros Hd1 Hd2.
  rewrite /nonsimilar /val_nonsimilar.
  destruct v1 as [lit1 | i1 recs1 | gen1 tag1 [|v1' vs1']],
           v2 as [lit2 | i2 recs2 | gen2 tag2 [|v2' vs2']]; cbn; try done.
  - (* Lit/Lit *)
    destruct lit1, lit2; cbn; try done.
    intros Hns [= Heq]. apply Hns.
    apply (tr_loc_inj_on_dom _ Htr) in Heq; [by subst| set_solver..].
  - (* Lit/Block-empty *)
    destruct lit1; cbn; done.
  - (* Block-empty/Lit *)
    destruct lit2; cbn; done.
  - (* Block-nonempty/Block-nonempty *)
    destruct gen1 as [bid1|], gen2 as [bid2|]; cbn; try done.
    destruct bid1 as [bid1|], bid2 as [bid2|]; try done.
    cbn. intros [Hbid|[Htag|Hvs]].
    + by left.
    + right. by left.
    + right. right. intros Heq. apply Hvs.
      injection Heq as Hh Ht.
      apply (tr_val_inj _ Htr) in Hh; [|set_solver..]. subst.
      f_equal. apply (tr_val_list_inj _ Htr); [set_solver..|done].
Qed.

Lemma tr_val_immediate ψ v :
  val_immediate v → val_immediate (tr_val ψ v).
Proof.
  destruct v as [lit | i recs | gen tag [|v' vs']]; cbn; try done.
  destruct lit; done.
Qed.

Lemma tr_subst_list ψ xs vs e :
  tr_expr ψ (subst_list xs vs e) = subst_list xs (tr_val ψ <$> vs) (tr_expr ψ e).
Proof.
  revert vs e. induction xs as [|x' xs IH]; intros [|v' vs'] e0; cbn; try done.
  rewrite tr_subst'. f_equal. apply IH.
Qed.

Lemma tr_eval_match_block ψ gen tag vs x e brs e' :
  eval_match tag (length vs) (SubjectBlock gen vs) x e brs = Some e' →
  eval_match tag (length (tr_val ψ <$> vs))
    (SubjectBlock gen (tr_val ψ <$> vs)) x (tr_expr ψ e)
    ((λ br, (br.1, tr_expr ψ br.2)) <$> brs) = Some (tr_expr ψ e').
Proof.
  rewrite length_fmap.
  revert e'. induction brs as [|br brs' IH]; intros e' Heq; cbn in *.
  - injection Heq as <-. rewrite tr_subst'. done.
  - case_match; cbn in *.
    + injection Heq as <-. by rewrite tr_subst_list tr_subst'.
    + by apply IH.
Qed.

Lemma tr_eval_match_loc ψ tag sz l x e brs e' :
  eval_match tag sz (SubjectLoc l) x e brs = Some e' →
  eval_match tag sz (SubjectLoc (tr_loc ψ l)) x (tr_expr ψ e)
    ((λ br, (br.1, tr_expr ψ br.2)) <$> brs) = Some (tr_expr ψ e').
Proof.
  revert e'. induction brs as [|br brs' IH]; intros e' Heq; cbn in *.
  - injection Heq as <-. rewrite tr_subst'. done.
  - case_match; cbn in *.
    + case_match; cbn in *; last done.
      injection Heq as <-. by rewrite tr_subst'.
    + by apply IH.
Qed.

Lemma locs_eval_app recs x v e :
  locs_expr (eval_app recs x v e) ⊆
    locs_val v ∪ locs_expr e ∪ ⋃ ((λ r, locs_expr r.2) <$> recs).
Proof.
  rewrite /eval_app /eval_app' /eval_app_aux /foldri.
  enough (∀ rs i,
    locs_expr
      (foldri' (λ j rec acc, subst' rec.1.1 (ValRecs j recs) acc)
               (subst' x v e) rs i)
    ⊆ locs_val v ∪ locs_expr e ∪ ⋃ ((λ r, locs_expr r.2) <$> recs))
    as H by apply H.
  intros rs. induction rs as [|r rs' IH]; intros i; simpl.
  - pose proof (locs_subst' x v e). set_solver.
  - pose proof (locs_subst' r.1.1 (ValRecs i recs)
      (foldri' (λ j rec acc, subst' rec.1.1 (ValRecs j recs) acc)
               (subst' x v e) rs' (S i))) as Hs.
    simpl in Hs. specialize (IH (S i)). set_solver.
Qed.

Lemma tr_eval_app ψ recs rec_b1 v rec_e :
  tr_expr ψ (eval_app recs rec_b1 v rec_e) =
  eval_app ((λ r, (r.1, tr_expr ψ r.2)) <$> recs) rec_b1 (tr_val ψ v) (tr_expr ψ rec_e).
Proof.
  rewrite /eval_app /eval_app' /eval_app_aux.
  rewrite foldri_fmap.
  rewrite -(tr_subst' ψ rec_b1 v rec_e).
  symmetry. apply (foldri_comm _ (tr_expr ψ)).
  intros i x acc. cbn. by rewrite tr_subst'.
Qed.

(** Translation preserves "is a value": if [e] is not a value, then
    [tr_expr ψ e] is not a value either. *)
Lemma tr_expr_to_val_None ψ e :
  to_val e = None → to_val (tr_expr ψ e) = None.
Proof. by destruct e. Qed.

Lemma tr_expr_inv_rec ψ e f x e0 :
  tr_expr ψ e = Rec f x e0 →
  ∃ e0', e = Rec f x e0' ∧ tr_expr ψ e0' = e0.
Proof.
  destruct e; simpl; intros Heq; try discriminate.
  inversion Heq; subst; eauto.
Qed.


Lemma tr_expr_inv_val ψ e v :
  tr_expr ψ e = Val v →
  ∃ v', e = Val v' ∧ tr_val ψ v' = v.
Proof.
  destruct e; simpl; intros Heq; try discriminate.
  inversion Heq; subst; eauto.
Qed.

Lemma tr_expr_inv_let ψ e x e1 e2 :
  tr_expr ψ e = Let x e1 e2 →
  ∃ e1' e2', e = Let x e1' e2' ∧ tr_expr ψ e1' = e1 ∧ tr_expr ψ e2' = e2.
Proof.
  destruct e; simpl; intros Heq; try discriminate.
  inversion Heq; subst; eauto.
Qed.

Lemma tr_expr_inv_if ψ e e0 e1 e2 :
  tr_expr ψ e = If e0 e1 e2 →
  ∃ e0' e1' e2', e = If e0' e1' e2' ∧ tr_expr ψ e0' = e0 ∧ tr_expr ψ e1' = e1 ∧ tr_expr ψ e2' = e2.
Proof.
  destruct e; simpl; intros Heq; try discriminate.
  inversion Heq; subst; eauto 10.
Qed.

Lemma tr_expr_inv_for ψ e e0 e1 e2 :
  tr_expr ψ e = For e0 e1 e2 →
  ∃ e0' e1' e2', e = For e0' e1' e2' ∧ tr_expr ψ e0' = e0 ∧ tr_expr ψ e1' = e1 ∧ tr_expr ψ e2' = e2.
Proof.
  destruct e; simpl; intros Heq; try discriminate.
  inversion Heq; subst; eauto 10.
Qed.

Lemma tr_expr_inv_equal ψ e e1 e2 :
  tr_expr ψ e = Equal e1 e2 →
  ∃ e1' e2', e = Equal e1' e2' ∧ tr_expr ψ e1' = e1 ∧ tr_expr ψ e2' = e2.
Proof.
  destruct e; simpl; intros Heq; try discriminate.
  inversion Heq; subst; eauto.
Qed.

Lemma tr_val_inv_litbool ψ v b :
  tr_val ψ v = #(LitBool b) → v = #(LitBool b).
Proof.
  destruct v; simpl; intros Heq; try discriminate.
  destruct lit; simpl in Heq; inversion Heq; subst; done.
Qed.

Lemma tr_val_inv_litint ψ v n :
  tr_val ψ v = #(LitInt n) → v = #(LitInt n).
Proof.
  destruct v; simpl; intros Heq; try discriminate.
  destruct lit; simpl in Heq; inversion Heq; subst; done.
Qed.

Lemma tr_expr_inv_app ψ e e1 e2 :
  tr_expr ψ e = App e1 e2 →
  ∃ e1' e2', e = App e1' e2' ∧ tr_expr ψ e1' = e1 ∧ tr_expr ψ e2' = e2.
Proof.
  destruct e; simpl; intros Heq; try discriminate.
  inversion Heq; subst; eauto.
Qed.

Lemma tr_val_inv_block ψ v gen tag vs :
  tr_val ψ v = ValBlock gen tag vs →
  ∃ vs', v = ValBlock gen tag vs' ∧ tr_val ψ <$> vs' = vs.
Proof.
  destruct v; simpl; intros Heq; try discriminate.
  inversion Heq; subst; eauto.
Qed.

Lemma tr_val_inv_loc ψ v l :
  tr_val ψ v = #(LitLoc l) →
  ∃ l', v = #(LitLoc l') ∧ tr_loc ψ l' = l.
Proof.
  destruct v; simpl; intros Heq; try discriminate.
  destruct lit; simpl in Heq; inversion Heq; subst; eauto.
Qed.

Lemma tr_val_inv_tuple_loc_int ψ v l fld :
  tr_val ψ v = ValTuple [ValLit (LitLoc l); ValLit (LitInt fld)] →
  ∃ l', v = ValTuple [ValLit (LitLoc l'); ValLit (LitInt fld)] ∧ tr_loc ψ l' = l.
Proof.
  intros Heq.
  apply tr_val_inv_block in Heq as (vs' & -> & Htrvs).
  destruct vs' as [|v1 [|v2 [|??]]]; simpl in Htrvs; try discriminate.
  inversion Htrvs as [[Hv1 Hv2]].
  apply tr_val_inv_loc in Hv1 as (l' & -> & Htrl).
  apply tr_val_inv_litint in Hv2 as ->.
  eauto.
Qed.

Lemma tr_expr_inv_match ψ e e0 x e1 brs :
  tr_expr ψ e = Match e0 x e1 brs →
  ∃ e0' e1' brs', e = Match e0' x e1' brs' ∧
                  tr_expr ψ e0' = e0 ∧
                  tr_expr ψ e1' = e1 ∧
                  ((λ br, (br.1, tr_expr ψ br.2)) <$> brs') = brs.
Proof.
  destruct e; simpl; intros Heq; try discriminate.
  inversion Heq; subst; eauto 10.
Qed.

Lemma tr_expr_inv_gettag ψ e e0 :
  tr_expr ψ e = GetTag e0 →
  ∃ e0', e = GetTag e0' ∧ tr_expr ψ e0' = e0.
Proof.
  destruct e; simpl; intros Heq; try discriminate.
  inversion Heq; subst; eauto.
Qed.

Lemma tr_expr_inv_getsize ψ e e0 :
  tr_expr ψ e = GetSize e0 →
  ∃ e0', e = GetSize e0' ∧ tr_expr ψ e0' = e0.
Proof.
  destruct e; simpl; intros Heq; try discriminate.
  inversion Heq; subst; eauto.
Qed.

Lemma tr_expr_inv_get_field ψ e (atm : atomicity) e1 e2 :
  tr_expr ψ e = GetField atm e1 e2 →
  ∃ e1' e2', e = GetField atm e1' e2' ∧ tr_expr ψ e1' = e1 ∧ tr_expr ψ e2' = e2.
Proof.
  destruct e; simpl; intros Heq; try discriminate.
  inversion Heq; subst; eauto.
Qed.

Lemma tr_expr_inv_set_field ψ e (atm : atomicity) e1 e2 e3 :
  tr_expr ψ e = SetField atm e1 e2 e3 →
  ∃ e1' e2' e3', e = SetField atm e1' e2' e3' ∧
                 tr_expr ψ e1' = e1 ∧ tr_expr ψ e2' = e2 ∧ tr_expr ψ e3' = e3.
Proof.
  destruct e; simpl; intros Heq; try discriminate.
  inversion Heq; subst; eauto 10.
Qed.

Lemma tr_expr_inv_xchg ψ e e1 e2 :
  tr_expr ψ e = Xchg e1 e2 →
  ∃ e1' e2', e = Xchg e1' e2' ∧ tr_expr ψ e1' = e1 ∧ tr_expr ψ e2' = e2.
Proof.
  destruct e; simpl; intros Heq; try discriminate.
  inversion Heq; subst; eauto.
Qed.

Lemma tr_expr_inv_cas ψ e e0 e1 e2 :
  tr_expr ψ e = CAS e0 e1 e2 →
  ∃ e0' e1' e2', e = CAS e0' e1' e2' ∧
                 tr_expr ψ e0' = e0 ∧ tr_expr ψ e1' = e1 ∧ tr_expr ψ e2' = e2.
Proof.
  destruct e; simpl; intros Heq; try discriminate.
  inversion Heq; subst; eauto 10.
Qed.

Lemma tr_expr_inv_faa ψ e e1 e2 :
  tr_expr ψ e = FAA e1 e2 →
  ∃ e1' e2', e = FAA e1' e2' ∧ tr_expr ψ e1' = e1 ∧ tr_expr ψ e2' = e2.
Proof.
  destruct e; simpl; intros Heq; try discriminate.
  inversion Heq; subst; eauto.
Qed.

Lemma tr_expr_inv_fork ψ e e0 :
  tr_expr ψ e = Fork e0 →
  ∃ e0', e = Fork e0' ∧ tr_expr ψ e0' = e0.
Proof.
  destruct e; simpl; intros Heq; try discriminate.
  inversion Heq; subst; eauto.
Qed.

Lemma tr_expr_inv_getlocal ψ e :
  tr_expr ψ e = GetLocal → e = GetLocal.
Proof. destruct e; simpl; intros Heq; congruence. Qed.

Lemma tr_expr_inv_setlocal ψ e e0 :
  tr_expr ψ e = SetLocal e0 →
  ∃ e0', e = SetLocal e0' ∧ tr_expr ψ e0' = e0.
Proof.
  destruct e; simpl; intros Heq; try discriminate.
  inversion Heq; subst; eauto.
Qed.

Lemma eval_match_block_some tag sz gen vs x e brs :
  ∃ e', eval_match tag sz (SubjectBlock gen vs) x e brs = Some e'.
Proof.
  induction brs as [|br brs IH]; simpl.
  - eauto.
  - case_match; simpl.
    + eauto.
    + apply IH.
Qed.

(** Reverse direction of [tr_eval_match_loc] for the [is_Some] predicate.
    Success of [eval_match] on a [SubjectLoc] subject only depends on the
    branches' pattern shapes (tag/length/[BAnon]-ness of fields), which are
    invariant under translation. *)
Lemma tr_eval_match_loc_some_inv ψ tag sz l x e brs e' :
  eval_match tag sz (SubjectLoc (tr_loc ψ l)) x (tr_expr ψ e)
    ((λ br, (br.1, tr_expr ψ br.2)) <$> brs) = Some e' →
  is_Some (eval_match tag sz (SubjectLoc l) x e brs).
Proof.
  revert e'. induction brs as [|br brs' IH]; intros e' Heq; cbn in *.
  - eauto.
  - case_match; cbn in *.
    + case_match; cbn in *; last done. eauto.
    + by eapply IH.
Qed.

(** [None]-preservation for [eval_match] under translation (location subject). *)
Lemma tr_eval_match_loc_none ψ tag sz l x e brs :
  eval_match tag sz (SubjectLoc l) x e brs = None →
  eval_match tag sz (SubjectLoc (tr_loc ψ l)) x (tr_expr ψ e)
    ((λ br, (br.1, tr_expr ψ br.2)) <$> brs) = None.
Proof.
  intros H.
  destruct (eval_match tag sz (SubjectLoc (tr_loc ψ l)) x (tr_expr ψ e)
              ((λ br, (br.1, tr_expr ψ br.2)) <$> brs)) eqn:E; [|done].
  apply tr_eval_match_loc_some_inv in E as [? E']. congruence.
Qed.

(** Reverse direction of [tr_eval_match_block] for the [is_Some] predicate. *)
Lemma tr_eval_match_block_some_inv ψ gen tag vs x e brs e' :
  eval_match tag (length (tr_val ψ <$> vs)) (SubjectBlock gen (tr_val ψ <$> vs))
    x (tr_expr ψ e) ((λ br, (br.1, tr_expr ψ br.2)) <$> brs) = Some e' →
  is_Some (eval_match tag (length vs) (SubjectBlock gen vs) x e brs).
Proof.
  rewrite length_fmap.
  revert e'. induction brs as [|br brs' IH]; intros e' Heq; cbn in *.
  - eauto.
  - case_match; cbn in *.
    + eauto.
    + by eapply IH.
Qed.

(** [None]-preservation for [eval_match] under translation (block subject). *)
Lemma tr_eval_match_block_none ψ gen tag vs x e brs :
  eval_match tag (length vs) (SubjectBlock gen vs) x e brs = None →
  eval_match tag (length (tr_val ψ <$> vs)) (SubjectBlock gen (tr_val ψ <$> vs))
    x (tr_expr ψ e) ((λ br, (br.1, tr_expr ψ br.2)) <$> brs) = None.
Proof.
  intros H.
  destruct (eval_match tag (length (tr_val ψ <$> vs)) (SubjectBlock gen (tr_val ψ <$> vs))
              x (tr_expr ψ e) ((λ br, (br.1, tr_expr ψ br.2)) <$> brs)) eqn:E; [|done].
  apply tr_eval_match_block_some_inv in E as [? E']. congruence.
Qed.

Lemma tr_expr_inv_emit ψ e e0 :
  tr_expr ψ e = Emit e0 →
  ∃ e0', e = Emit e0' ∧ tr_expr ψ e0' = e0.
Proof.
  destruct e; simpl; intros Heq; try discriminate.
  inversion Heq; subst; eauto.
Qed.

Lemma tr_expr_inv_block ψ e mut tag es :
  tr_expr ψ e = Block mut tag es →
  ∃ es', e = Block mut tag es' ∧ tr_expr ψ <$> es' = es.
Proof.
  destruct e; simpl; intros Heq; try discriminate.
  inversion Heq; subst; eauto.
Qed.

Lemma tr_expr_fmap_of_vals ψ es vs :
  tr_expr ψ <$> es = of_vals vs →
  ∃ vs', es = of_vals vs' ∧ tr_val ψ <$> vs' = vs.
Proof.
  revert vs. induction es as [|e es IH]; intros [|v vs] Heq.
  - exists []. done.
  - by inversion Heq.
  - by inversion Heq.
  - simpl in Heq. inversion Heq as [[He Hes]].
    apply tr_expr_inv_val in He as (v' & -> & Htrv).
    edestruct (IH vs Hes) as (vs' & -> & Hvs).
    exists (v' :: vs'). split; first done.
    rewrite fmap_cons Htrv Hvs //.
Qed.

Lemma tr_expr_inv_alloc ψ e e1 e2 :
  tr_expr ψ e = Alloc e1 e2 →
  ∃ e1' e2', e = Alloc e1' e2' ∧ tr_expr ψ e1' = e1 ∧ tr_expr ψ e2' = e2.
Proof.
  destruct e; simpl; intros Heq; try discriminate.
  inversion Heq; subst; eauto.
Qed.

Lemma tr_expr_inv_unop ψ e op e0 :
  tr_expr ψ e = Unop op e0 →
  ∃ e0', e = Unop op e0' ∧ tr_expr ψ e0' = e0.
Proof.
  destruct e; simpl; intros Heq; try discriminate.
  inversion Heq; subst; eauto.
Qed.

Lemma tr_expr_inv_binop ψ e op e1 e2 :
  tr_expr ψ e = Binop op e1 e2 →
  ∃ e1' e2', e = Binop op e1' e2' ∧ tr_expr ψ e1' = e1 ∧ tr_expr ψ e2' = e2.
Proof.
  destruct e; simpl; intros Heq; try discriminate.
  inversion Heq; subst; eauto.
Qed.

Lemma tr_val_inv_recs ψ v i recs :
  tr_val ψ v = ValRecs i recs →
  ∃ recs', v = ValRecs i recs' ∧ (λ r : recursive, (r.1, tr_expr ψ r.2)) <$> recs' = recs.
Proof.
  destruct v; simpl; intros Heq; try discriminate.
  inversion Heq; subst; eauto.
Qed.

Lemma list_lookup_fmap_inv {A B} (f : A → B) (l : list A) i y :
  (f <$> l) !! i = Some y → ∃ x, l !! i = Some x ∧ f x = y.
Proof.
  rewrite list_lookup_fmap. destruct (l !! i) eqn:?; simpl; intros [=]; eauto.
Qed.
Lemma list_fmap_split {A B} (f : A → B) l ys1 y ys2 :
  f <$> l = ys1 ++ y :: ys2 →
  ∃ xs1 x xs2, l = xs1 ++ x :: xs2
    ∧ f <$> xs1 = ys1
    ∧ f x = y
    ∧ f <$> xs2 = ys2.
Proof.
  revert l. induction ys1 as [|y1 ys1 IH]; intros [|x xs] Heq; simpl in Heq; try by inversion Heq.
  - inversion Heq; subst. by exists [], x, xs.
  - inversion Heq as [[Hy Hxs]].
    edestruct (IH xs Hxs) as (xs1 & x' & xs2 & -> & Hys1 & Hx & Hys2).
    exists (x :: xs1), x', xs2. split_and!; try done.
    rewrite fmap_cons Hy. f_equal. done.
Qed.

Lemma tr_expr_unfilli ψ k e e_hole :
  tr_expr ψ e = filli k e_hole →
  ∃ k_src e_src, e = filli k_src e_src
    ∧ tr_expr ψ e_src = e_hole
    ∧ tr_ectxi ψ k_src = k.
Proof.
  revert e e_hole. induction k; intros e e_hole Heq; simpl in Heq.
  - (* CtxApp1 *)
    apply tr_expr_inv_app in Heq as (e1' & e2' & -> & Htr1 & Htr2).
    apply tr_expr_inv_val in Htr2 as (v' & -> & Htrv).
    exists (CtxApp1 v'), e1'. simpl. by rewrite Htrv.
  - (* CtxApp2 *)
    apply tr_expr_inv_app in Heq as (e1' & e2' & -> & Htr1 & Htr2).
    exists (CtxApp2 e1'), e2'. simpl. by rewrite Htr1.
  - (* CtxLet *)
    apply tr_expr_inv_let in Heq as (e1' & e2' & -> & Htr1 & Htr2).
    exists (CtxLet x e2'), e1'. simpl. by rewrite Htr2.
  - (* CtxUnop *)
    apply tr_expr_inv_unop in Heq as (e0' & -> & Htr0).
    exists (CtxUnop op), e0'. by simpl.
  - (* CtxBinop1 *)
    apply tr_expr_inv_binop in Heq as (e1' & e2' & -> & Htr1 & Htr2).
    apply tr_expr_inv_val in Htr2 as (v' & -> & Htrv).
    exists (CtxBinop1 op v'), e1'. simpl. by rewrite Htrv.
  - (* CtxBinop2 *)
    apply tr_expr_inv_binop in Heq as (e1' & e2' & -> & Htr1 & Htr2).
    exists (CtxBinop2 op e1'), e2'. simpl. by rewrite Htr1.
  - (* CtxEqual1 *)
    apply tr_expr_inv_equal in Heq as (e1' & e2' & -> & Htr1 & Htr2).
    apply tr_expr_inv_val in Htr2 as (v' & -> & Htrv).
    exists (CtxEqual1 v'), e1'. simpl. by rewrite Htrv.
  - (* CtxEqual2 *)
    apply tr_expr_inv_equal in Heq as (e1' & e2' & -> & Htr1 & Htr2).
    exists (CtxEqual2 e1'), e2'. simpl. by rewrite Htr1.
  - (* CtxIf *)
    apply tr_expr_inv_if in Heq as (e0' & e1' & e2' & -> & Htr0 & Htr1 & Htr2).
    exists (CtxIf e1' e2'), e0'. simpl. by rewrite Htr1 Htr2.
  - (* CtxFor1 *)
    apply tr_expr_inv_for in Heq as (e0' & e1' & e2' & -> & Htr0 & Htr1 & Htr2).
    exists (CtxFor1 e1' e2'), e0'. simpl. by rewrite Htr1 Htr2.
  - (* CtxFor2 *)
    apply tr_expr_inv_for in Heq as (e0' & e1' & e2' & -> & Htr0 & Htr1 & Htr2).
    apply tr_expr_inv_val in Htr0 as (v' & -> & Htrv).
    exists (CtxFor2 v' e2'), e1'. simpl. by rewrite Htrv Htr2.
  - (* CtxAlloc1 *)
    apply tr_expr_inv_alloc in Heq as (e1' & e2' & -> & Htr1 & Htr2).
    apply tr_expr_inv_val in Htr2 as (v' & -> & Htrv).
    exists (CtxAlloc1 v'), e1'. simpl. by rewrite Htrv.
  - (* CtxAlloc2 *)
    apply tr_expr_inv_alloc in Heq as (e1' & e2' & -> & Htr1 & Htr2).
    exists (CtxAlloc2 e1'), e2'. simpl. by rewrite Htr1.
  - (* CtxBlock *)
    apply tr_expr_inv_block in Heq as (es' & -> & Htres).
    apply list_fmap_split in Htres as (es_l & e_src & es_r & -> & Hl & He & Hr).
    apply tr_expr_fmap_of_vals in Hr as (vs_src & -> & Hvs).
    exists (CtxBlock mut tag es_l vs_src), e_src. split_and!; try done.
    simpl. f_equal.
    + change (map (tr_expr ψ) es_l) with (tr_expr ψ <$> es_l). exact Hl.
    + change (map (tr_val ψ) vs_src) with (tr_val ψ <$> vs_src). exact Hvs.
  - (* CtxMatch *)
    apply tr_expr_inv_match in Heq as (e0' & e1' & brs' & -> & Htr0 & Htr1 & Htrbrs).
    exists (CtxMatch x e1' brs'), e0'. split_and!; try done.
    simpl. rewrite Htr1. f_equal.
    change (map (λ br, (br.1, tr_expr ψ br.2)) brs')
      with ((λ br, (br.1, tr_expr ψ br.2)) <$> brs').
    exact Htrbrs.
  - (* CtxGetTag *)
    apply tr_expr_inv_gettag in Heq as (e0' & -> & Htr0).
    exists CtxGetTag, e0'. by simpl.
  - (* CtxGetSize *)
    apply tr_expr_inv_getsize in Heq as (e0' & -> & Htr0).
    exists CtxGetSize, e0'. by simpl.
  - (* CtxGetField1 *)
    apply tr_expr_inv_get_field in Heq as (e1' & e2' & -> & Htr1 & Htr2).
    apply tr_expr_inv_val in Htr2 as (v' & -> & Htrv).
    exists (CtxGetField1 atm v'), e1'. simpl. by rewrite Htrv.
  - (* CtxGetField2 *)
    apply tr_expr_inv_get_field in Heq as (e1' & e2' & -> & Htr1 & Htr2).
    exists (CtxGetField2 atm e1'), e2'. simpl. by rewrite Htr1.
  - (* CtxSetField1 *)
    apply tr_expr_inv_set_field in Heq as (e1' & e2' & e3' & -> & Htr1 & Htr2 & Htr3).
    apply tr_expr_inv_val in Htr2 as (v2' & -> & Htrv2).
    apply tr_expr_inv_val in Htr3 as (v3' & -> & Htrv3).
    exists (CtxSetField1 atm v2' v3'), e1'. simpl. by rewrite Htrv2 Htrv3.
  - (* CtxSetField2 *)
    apply tr_expr_inv_set_field in Heq as (e1' & e2' & e3' & -> & Htr1 & Htr2 & Htr3).
    apply tr_expr_inv_val in Htr3 as (v3' & -> & Htrv3).
    exists (CtxSetField2 atm e1' v3'), e2'. simpl. by rewrite Htr1 Htrv3.
  - (* CtxSetField3 *)
    apply tr_expr_inv_set_field in Heq as (e1' & e2' & e3' & -> & Htr1 & Htr2 & Htr3).
    exists (CtxSetField3 atm e1' e2'), e3'. simpl. by rewrite Htr1 Htr2.
  - (* CtxXchg1 *)
    apply tr_expr_inv_xchg in Heq as (e1' & e2' & -> & Htr1 & Htr2).
    apply tr_expr_inv_val in Htr2 as (v' & -> & Htrv).
    exists (CtxXchg1 v'), e1'. simpl. by rewrite Htrv.
  - (* CtxXchg2 *)
    apply tr_expr_inv_xchg in Heq as (e1' & e2' & -> & Htr1 & Htr2).
    exists (CtxXchg2 e1'), e2'. simpl. by rewrite Htr1.
  - (* CtxCAS0 *)
    apply tr_expr_inv_cas in Heq as (e0' & e1' & e2' & -> & Htr0 & Htr1 & Htr2).
    apply tr_expr_inv_val in Htr1 as (v1' & -> & Htrv1).
    apply tr_expr_inv_val in Htr2 as (v2' & -> & Htrv2).
    exists (CtxCAS0 v1' v2'), e0'. simpl. by rewrite Htrv1 Htrv2.
  - (* CtxCAS1 *)
    apply tr_expr_inv_cas in Heq as (e0' & e1' & e2' & -> & Htr0 & Htr1 & Htr2).
    apply tr_expr_inv_val in Htr2 as (v2' & -> & Htrv2).
    exists (CtxCAS1 e0' v2'), e1'. simpl. by rewrite Htr0 Htrv2.
  - (* CtxCAS2 *)
    apply tr_expr_inv_cas in Heq as (e0' & e1' & e2' & -> & Htr0 & Htr1 & Htr2).
    exists (CtxCAS2 e0' e1'), e2'. simpl. by rewrite Htr0 Htr1.
  - (* CtxFAA1 *)
    apply tr_expr_inv_faa in Heq as (e1' & e2' & -> & Htr1 & Htr2).
    apply tr_expr_inv_val in Htr2 as (v' & -> & Htrv).
    exists (CtxFAA1 v'), e1'. simpl. by rewrite Htrv.
  - (* CtxFAA2 *)
    apply tr_expr_inv_faa in Heq as (e1' & e2' & -> & Htr1 & Htr2).
    exists (CtxFAA2 e1'), e2'. simpl. by rewrite Htr1.
  - (* CtxSetLocal *)
    apply tr_expr_inv_setlocal in Heq as (e0' & -> & Htr0).
    exists CtxSetLocal, e0'. by simpl.
  - (* CtxEmit *)
    apply tr_expr_inv_emit in Heq as (e0' & -> & Htr0).
    exists CtxEmit, e0'. simpl. by rewrite Htr0.
Qed.

Lemma tr_expr_unfill ψ e K e' :
  tr_expr ψ e = fill K e' →
  to_val e' = None →
  ∃ K0 e0, e = fill K0 e0 ∧ tr_expr ψ e0 = e' ∧ tr_ectx ψ K0 = K.
Proof.
  revert e e'. induction K as [|K k IH] using rev_ind; intros e e' Heq Hnv.
  - exists [], e. by rewrite /fill /=.
  - rewrite /fill foldl_app /= in Heq.
    apply tr_expr_unfilli in Heq as (k_src & e_src & -> & Htr & Hk).
    edestruct (IH e_src e' Htr Hnv) as (K0 & e0 & -> & Htr0 & HK0).
    exists (K0 ++ [k_src]), e0. split.
    { rewrite /fill foldl_app /= //. }
    split; first done.
    rewrite /tr_ectx map_app /= Hk. f_equal.
    change (map (tr_ectxi ψ) K0) with (tr_ectx ψ K0). exact HK0.
Qed.
