(** * Tactics and instances for Mizzle's language

    Adapted from Zoo's [zoo/language/tactics.v] (the [reshape_expr]
    redex/context splitter and the [mizzle_simplify] / [invert_base_step]
    automation) followed by [zoo/language/typeclasses.v] (the [AsVal]
    instance [val_as_val], the [AsValRec] / [AsValRecs] / [AsValRecs']
    classes and their instances, and the [PureExec] instances [pure_*]).
    The [AsVal] and [Context] classes themselves live in [semantics.v]. The tactics come
    first because the instances lean on them. *)

From mizzle.lang Require Import
  prelude.
From mizzle.lang Require Export
  semantics.
From mizzle.lang Require Import
  options.

(** ** Tactics *)

Ltac reshape_expr e tac :=
  let rec go K e :=
    match e with
    | _ =>
        tac K e
    | App ?e1 (Val ?v2) =>
        add_ectxi (CtxApp1 v2) K e1
    | App ?e1 ?e2 =>
        add_ectxi (CtxApp2 e1) K e2
    | Let ?x ?e1 ?e2 =>
        add_ectxi (CtxLet x e2) K e1
    | Unop ?op ?e =>
        add_ectxi (CtxUnop op) K e
    | Binop ?op ?e1 (Val ?v2) =>
        add_ectxi (CtxBinop1 op v2) K e1
    | Binop ?op ?e1 ?e2 =>
        add_ectxi (CtxBinop2 op e1) K e2
    | Equal ?e1 (Val ?v2) =>
        add_ectxi (CtxEqual1 v2) K e1
    | Equal ?e1 ?e2 =>
        add_ectxi (CtxEqual2 e1) K e2
    | If ?e0 ?e1 ?e2 =>
        add_ectxi (CtxIf e1 e2) K e0
    | For (Val ?v1) ?e2 ?e3 =>
        add_ectxi (CtxFor2 v1 e3) K e2
    | For ?e1 ?e2 ?e3 =>
        add_ectxi (CtxFor1 e2 e3) K e1
    | Alloc ?e1 (Val ?v2) =>
        add_ectxi (CtxAlloc1 v2) K e1
    | Alloc ?e1 ?e2 =>
        add_ectxi (CtxAlloc2 e1) K e2
    | Block ?mut ?tag ?es =>
        go_list K (CtxBlock mut tag) es
    | Match ?e0 ?x ?e1 ?brs =>
        add_ectxi (CtxMatch x e1 brs) K e0
    | GetTag ?e =>
        add_ectxi CtxGetTag K e
    | GetSize ?e =>
        add_ectxi CtxGetSize K e
    | GetField ?atm ?e1 (Val ?v2) =>
        add_ectxi (CtxGetField1 atm v2) K e1
    | GetField ?atm ?e1 ?e2 =>
        add_ectxi (CtxGetField2 atm e1) K e2
    | SetField ?atm ?e1 (Val ?v2) (Val ?v3) =>
        add_ectxi (CtxSetField1 atm v2 v3) K e1
    | SetField ?atm ?e1 ?e2 (Val ?v3) =>
        add_ectxi (CtxSetField2 atm e1 v3) K e2
    | SetField ?atm ?e1 ?e2 ?e3 =>
        add_ectxi (CtxSetField3 atm e1 e2) K e3
    | Xchg ?e1 (Val ?v2) =>
        add_ectxi (CtxXchg1 v2) K e1
    | Xchg ?e1 ?e2 =>
        add_ectxi (CtxXchg2 e1) K e2
    | CAS ?e0 (Val ?v1) (Val ?v2) =>
        add_ectxi (CtxCAS0 v1 v2) K e0
    | CAS ?e0 ?e1 (Val ?v2) =>
        add_ectxi (CtxCAS1 e0 v2) K e1
    | CAS ?e0 ?e1 ?e2 =>
        add_ectxi (CtxCAS2 e0 e1) K e2
    | FAA ?e1 (Val ?v2) =>
        add_ectxi (CtxFAA1 v2) K e1
    | FAA ?e1 ?e2 =>
        add_ectxi (CtxFAA2 e1) K e2
    | SetLocal ?e =>
        add_ectxi CtxSetLocal K e
    | Emit ?e =>
        add_ectxi CtxEmit K e
    end
  with go_list K ctx es :=
    let es := eval simpl in (rev es) in
    go_list' K ctx es (@nil val)
  with go_list' K ctx es vs :=
    lazymatch es with
    | cons ?e ?es =>
        lazymatch e with
        | Val ?v =>
            go_list' K ctx es (cons v vs)
        | _ =>
            add_ectxi (ctx (rev es) vs) K e
        end
    | _ =>
        fail
    end
  with add_ectxi k K e :=
    go (cons k K) e
  in
  go (@nil ectxi) e.

Tactic Notation "mizzle_fold_typeclasses" "in" hyp(H) :=
  try match type of H with
  | val_nonsimilar _ _ =>
      change val_nonsimilar with (@nonsimilar val val_nonsimilar) in H
  | val_similar _ _ =>
      change val_similar with (@similar val val_similar) in H
  end.
Tactic Notation "mizzle_fold_typeclasses" :=
  try match goal with
  | |- val_nonsimilar _ _ =>
      change val_nonsimilar with (@nonsimilar val val_nonsimilar)
  | |- val_similar _ _ =>
      change val_similar with (@similar val val_similar)
  end.
Tactic Notation "mizzle_fold_typeclasses" "in" "*" :=
  repeat_on_hyps (fun H =>
    mizzle_fold_typeclasses in H
  );
  mizzle_fold_typeclasses.

Tactic Notation "mizzle_simpl" "in" hyp(H) :=
  simpl in H;
  mizzle_fold_typeclasses in H.
Tactic Notation "mizzle_simpl" :=
  simpl;
  mizzle_fold_typeclasses.

Tactic Notation "mizzle_simplify" "in" hyp(H) :=
  mizzle_simpl in H;
  try match type of H with
  | to_val _ = Some _ =>
      apply of_to_val in H

  | @nonsimilar val _ (ValLit (LitBool _)) (ValLit (LitBool _)) =>
      apply val_nonsimilar_bool in H
  | @nonsimilar val _ (ValLit (LitInt (Z.of_nat _))) (ValLit (LitInt (Z.of_nat _))) =>
      apply val_nonsimilar_nat in H
  | @nonsimilar val _ (ValLit (LitInt _)) (ValLit (LitInt _)) =>
      apply val_nonsimilar_int in H
  | @nonsimilar val _ (ValLit (LitLoc _)) (ValLit (LitLoc _)) =>
      apply val_nonsimilar_location in H
  | @nonsimilar val _ (ValBlock _ _ nil) (ValBlock _ _ nil) =>
      apply val_nonsimilar_block_empty in H
  | @nonsimilar val _ (ValBlock (Generative (Some _)) _ _) (ValBlock (Generative (Some _)) _ _) =>
      apply val_nonsimilar_block_generative in H; try done

  | @similar val _ (ValLit (LitBool _)) (ValLit (LitBool _)) =>
      apply val_similar_bool in H
  | @similar val _ (ValLit (LitInt (Z.of_nat _))) (ValLit (LitInt (Z.of_nat _))) =>
      apply val_similar_nat in H
  | @similar val _ (ValLit (LitInt _)) (ValLit (LitInt _)) =>
      apply val_similar_int in H
  | @similar val _ (ValLit (LitLoc _)) (ValLit (LitLoc _)) =>
      apply val_similar_location in H
  | @similar val _ (ValBlock _ _ nil) (ValBlock _ _ nil) =>
      apply val_similar_block_empty in H
  | @similar val _ (ValBlock _ _ nil) (ValBlock _ _ (cons _ _)) =>
      apply val_similar_block_empty_1 in H as []
  | @similar val _ (ValBlock _ _ (cons _ _)) (ValBlock _ _ nil) =>
      apply val_similar_block_empty_2 in H as []
  | @similar val _ (ValBlock (Generative _) _ _) (ValBlock (Generative _) _ _) =>
      let H1 := fresh in
      let H2 := fresh in
      let H3 := fresh in
      apply val_similar_block_generative in H as (H1 & H2 & H3); last naive_solver;
      mizzle_simpl in H1;
      mizzle_simpl in H2;
      mizzle_simpl in H3
  | @similar val _ (ValBlock Nongenerative _ _) (ValBlock Nongenerative _ _) =>
      let H1 := fresh in
      let H2 := fresh in
      apply val_similar_block_nongenerative in H as (H1 & H2);
      mizzle_simpl in H1;
      mizzle_simpl in H2
  | @similar val _ (ValLit (LitLoc _)) (ValBlock _ _ _) =>
      apply val_similar_location_block in H as []
  | @similar val _ (ValBlock _ _ _) (ValLit (LitLoc _)) =>
      apply val_similar_block_location in H as []
  | @similar val _ (ValBlock (Generative _) _ _) (ValBlock Nongenerative _ _) =>
      apply val_similar_block_generative_nongenerative in H as []; done
  | @similar val _ (ValBlock Nongenerative _ _) (ValBlock (Generative _) _ _) =>
      apply val_similar_block_nongenerative_generative in H as []; done
  end;
  try mizzle_simpl in H.
Tactic Notation "mizzle_simplify" :=
  repeat_on_hyps (fun H =>
    mizzle_simplify in H
  );
  simplify_eq/=;
  mizzle_fold_typeclasses in *.

Ltac invert_base_step :=
  simpl in *;
  repeat match goal with
  | H: base_step _ ?e _ _ _ _ _ |- _ =>
      try (is_var e; fail 1);
      invert H
  end;
  mizzle_simplify.

Create HintDb mizzle.

#[global] Hint Resolve
  val_similar_refl

  base_reducible_no_obs_equal
  base_reducible_equal
  reducible_equal

  base_reducible_no_obs_cas
  base_reducible_cas
  reducible_cas
: mizzle.

#[global] Hint Extern 0 (
  @nonsimilar val _ _ _
) => (
  progress simpl; try injection
) : mizzle.
#[global] Hint Extern 0 (
  @similar val _ _ _
) => (
  progress simpl
) : mizzle.

#[global] Hint Extern 0 (
  base_reducible _ _ _
) =>
  do 4 eexists; simpl
: mizzle.
#[global] Hint Extern 0 (
  base_reducible_no_obs _ _ _
) =>
  do 3 eexists; simpl
: mizzle.

#[global] Hint Extern 1 (
  base_step _ _ _ _ _ _ _
) =>
  econstructor
: mizzle.
#[global] Hint Extern 0 (
  base_step _ (Equal _ _) _ _ _ _ _
) =>
  eapply base_step_equal_fail;
  simpl; try naive_solver done
: mizzle.
#[global] Hint Extern 0 (
  base_step _ (Equal _ _) _ _ _ _ _
) =>
  eapply base_step_equal_success;
  simpl
: mizzle.
#[global] Hint Extern 0 (
  base_step _ (Alloc _ _) _ _ _ _ _
) =>
  apply base_step_alloc'
: mizzle.
#[global] Hint Extern 0 (
  base_step _ (Block Mutable _ _) _ _ _ _ _
) =>
  eapply base_step_block_mutable'
: mizzle.
#[global] Hint Extern 0 (
  base_step _ (Block ImmutableGenerativeStrong _ _) _ _ _ _ _
) =>
  eapply base_step_block_immutable_generative_strong'
: mizzle.
#[global] Hint Extern 0 (
  base_step _ (CAS _ _ _) _ _ _ _ _
) =>
  eapply base_step_cas_fail;
  [ try done
  | simpl; try naive_solver done
  ]
: mizzle.
#[global] Hint Extern 0 (
  base_step _ (CAS _ _ _) _ _ _ _ _
) =>
  eapply base_step_cas_success;
  simpl
: mizzle.
#[global] Hint Extern 0 (
  base_step _ (Fork _) _ _ _ _ _
) =>
  apply base_step_fork'
: mizzle.

(** ** Instances *)

Implicit Types e : expr.
Implicit Types v : val.

#[global] Instance val_as_val v :
  AsVal (Val v) v.
Proof.
  done.
Qed.

Class AsValRec v f x e :=
  as_ValRec : v = ValRec f x e.
#[global] Hint Mode AsValRec ! - - - : typeclass_instances.

Lemma ValRec_as_ValRec f x e :
  AsValRec (ValRec f x e) f x e.
Proof.
  done.
Qed.
#[global] Hint Extern 0 (
  AsValRec (ValRec _ _ _) _ _ _
) =>
  apply ValRec_as_ValRec
: typeclass_instances.

Class AsValRecs v i recs vs :=
  as_ValRecs :
    Foralli (λ i v, v = ValRecs i recs) vs ∧
    v = ValRecs i recs ∧
    length recs = length vs.
#[global] Hint Mode AsValRecs ! - - - : typeclass_instances.

#[global] Instance as_ValRec_as_ValRecs v f x e :
  AsValRec v f x e →
  AsValRecs v 0 [(f, x, e)] [v].
Proof.
  done.
Qed.

Class AsValRecs' v i recs vs :=
  as_ValRecs' : AsValRecs v i recs vs.

Lemma as_ValRecs'_as_ValRecs v i recs vs :
  AsValRecs' v i recs vs →
  AsValRecs v i recs vs.
Proof.
  done.
Qed.

Section pure_exec.
  #[local] Ltac solve_exec_safe :=
    intros; subst;
    eauto with mizzle.
  #[local] Ltac solve_exec_puredet :=
    intros;
    invert_base_step;
    try naive_solver.
  #[local] Ltac solve_pure_exec :=
    intros ?; destruct_and?;
    apply nsteps_once, pure_base_step_pure_step;
    try (case_bool_decide; first subst);
    (split; [solve_exec_safe | solve_exec_puredet]).

  #[global] Instance pure_rec f x e :
    PureExec
      True
      1
      (Rec f x e)
      (Val $ ValRec f x e).
  Proof.
    solve_pure_exec.
  Qed.

  #[global] Instance pure_app v1 i recs rec vs v2 `{HAsValRecs : !AsValRecs v1 i recs vs} :
    PureExec
      (recs !! i = Some rec)
      1
      (App (Val v1) (Val v2))
      (foldr2 (λ rec v, subst' rec.1.1 v) (subst' rec.1.2 v2 rec.2) recs vs).
  Proof.
    destruct HAsValRecs as (Hvs & -> & Hlength) => Hlookup.
    apply nsteps_once, pure_base_step_pure_step.
    split; first solve_exec_safe.
    intros tid σ1 κ e σ2 es Hstep.
    invert_base_step.
    split_and!; try done.
    enough (
      ∀ recs1 recs2 vs1 vs2 e,
      recs = recs1 ++ recs2 →
      vs = vs1 ++ vs2 →
      length recs1 = length vs1 →
        foldri (λ i rec, subst' rec.1.1 (ValRecs i recs)) e recs1 =
        foldr2 (λ rec v, subst' rec.1.1 v) e recs1 vs1
    ) as H.
    { apply (H _ [] _ []); last done.
      all: rewrite right_id //.
    }
    clear- Hvs Hlength.
    induction recs1 as [| rec recs1 IH] using rev_ind => recs2 vs1 vs2 e Hrecs_eq Hvs_eq Hlength1; first done.
    destruct vs1 as [| v vs1 _] using rev_ind.
    all: simpl_length/= in Hlength1.
    1: lia.
    rewrite foldri_app foldr2_app /=; first lia.
    assert (ValRecs (length recs1) recs = v) as ->.
    { eapply Foralli_lookup_1 in Hvs; first done.
      rewrite Hvs_eq lookup_app_l.
      { simpl_length/=. lia. }
      rewrite lookup_snoc_Some. naive_solver lia.
    }
    apply (IH (rec :: recs2) vs1 (v :: vs2)).
    { rewrite Hrecs_eq -assoc //. }
    { rewrite Hvs_eq -assoc //. }
    { lia. }
  Qed.
  #[global] Instance pure_app_rec f x v1 v2 :
    PureExec True 1 (App (Val $ ValRec f x (Val v1)) (Val v2)) (Val v1).
  Proof.
    pose proof (pure_app (ValRec f x (Val v1)) 0 [(f, x, Val v1)] (f, x, Val v1) [ValRec f x (Val v1)] v2) as H.
    rewrite /= !subst'_val in H.
    intros _. naive_solver.
  Qed.

  #[global] Instance pure_let x v1 e2 :
    PureExec
      True
      1
      (Let x (Val v1) e2)
      (subst' x v1 e2).
    Proof.
      solve_pure_exec.
    Qed.

  #[global] Instance pure_unop op v v' :
    PureExec
      (eval_unop op v = Some v')
      1
      (Unop op (Val v))
      (Val v').
  Proof.
    solve_pure_exec.
  Qed.

  #[global] Instance pure_binop op v1 v2 v' :
    PureExec
      (eval_binop op v1 v2 = Some v')
      1
      (Binop op (Val v1) (Val v2))
      (Val v').
  Proof.
    solve_pure_exec.
  Qed.

  #[global] Instance pure_equal_bool b1 b2 :
    PureExec
      True
      1
      (Equal (Val $ ValBool b1) (Val $ ValBool b2))
      (Val $ ValBool (bool_decide (b1 = b2))).
  Proof.
    solve_pure_exec.
  Qed.
  #[global] Instance pure_equal_int i1 i2 :
    PureExec
      True
      1
      (Equal (Val $ ValInt i1) (Val $ ValInt i2))
      (Val $ ValBool (bool_decide (i1 = i2))).
  Proof.
    solve_pure_exec.
  Qed.
  #[global] Instance pure_equal_location l1 l2 :
    PureExec
      True
      1
      (Equal (Val $ ValLoc l1) (Val $ ValLoc l2))
      (Val $ ValBool (bool_decide (l1 = l2))).
  Proof.
    solve_pure_exec.
  Qed.
  #[global] Instance pure_equal_location_block l gen tag vs :
    PureExec
      True
      1
      (Equal (Val $ ValLoc l) (Val $ ValBlock gen tag vs))
      (Val $ ValBool false).
  Proof.
    solve_pure_exec.
  Qed.
  #[global] Instance pure_equal_block_location gen tag vs l :
    PureExec
      True
      1
      (Equal (Val $ ValBlock gen tag vs) (Val $ ValLoc l))
      (Val $ ValBool false).
  Proof.
    solve_pure_exec.
  Qed.
  #[global] Instance pure_equal_block_generative bid tag vs :
    PureExec
      True
      1
      (Equal (Val $ ValBlock (Generative (Some bid)) tag vs) (Val $ ValBlock (Generative (Some bid)) tag vs))
      (Val $ ValBool true).
  Proof.
    destruct vs; solve_pure_exec.
  Qed.
  #[global] Instance pure_equal_block_generative_nongenerative bid1 tag1 vs1 tag2 vs2 :
    PureExec
      (length vs1 ≠ 0 ∨ length vs2 ≠ 0)
      1
      (Equal (Val $ ValBlock (Generative bid1) tag1 vs1) (Val $ ValBlock Nongenerative tag2 vs2))
      (Val $ ValBool false).
  Proof.
    solve_pure_exec.
  Qed.
  #[global] Instance pure_equal_block_nongenerative_generative tag1 vs1 bid2 tag2 vs2 :
    PureExec
      (length vs1 ≠ 0 ∨ length vs2 ≠ 0)
      1
      (Equal (Val $ ValBlock Nongenerative tag1 vs1) (Val $ ValBlock (Generative bid2) tag2 vs2))
      (Val $ ValBool false).
  Proof.
    solve_pure_exec.
  Qed.
  #[global] Instance pure_equal_block_empty tag1 tag2 :
    PureExec
      True
      1
      (Equal (Val $ ValBlock Nongenerative tag1 []) (Val $ ValBlock Nongenerative tag2 []))
      (Val $ ValBool (bool_decide (tag1 = tag2))).
  Proof.
    solve_pure_exec.
  Qed.
  #[global] Instance pure_equal_block_empty_1 gen1 tag1 gen2 tag2 v2 vs2 :
    PureExec
      True
      1
      (Equal (Val $ ValBlock gen1 tag1 []) (Val $ ValBlock gen2 tag2 (v2 :: vs2)))
      (Val $ ValBool false).
  Proof.
    solve_pure_exec.
  Qed.
  #[global] Instance pure_equal_block_empty_2 gen1 tag1 v1 vs1 gen2 tag2 :
    PureExec
      True
      1
      (Equal (Val $ ValBlock gen1 tag1 (v1 :: vs1)) (Val $ ValBlock gen2 tag2 []))
      (Val $ ValBool false).
  Proof.
    solve_pure_exec.
  Qed.

  #[global] Instance pure_if_true e1 e2 :
    PureExec
      True
      1
      (If (Val $ ValBool true) e1 e2)
      e1.
  Proof.
    solve_pure_exec.
  Qed.
  #[global] Instance pure_if_false e1 e2 :
    PureExec
      True
      1
      (If (Val $ ValBool false) e1 e2)
      e2.
  Proof.
    solve_pure_exec.
  Qed.

  Lemma pure_while e0 e1 :
    PureExec
      True
      1
      (While e0 e1)
      (If e0 (Seq e1 (While e0 e1)) Unit).
  Proof.
    solve_pure_exec.
  Qed.

  Lemma pure_for n1 n2 e :
    PureExec
      True
      1
      (For (Val $ ValInt n1) (Val $ ValInt n2) e)
      (if decide (n2 ≤ n1)%Z then Unit else Seq (App e (Val $ ValInt n1)) (For (Val $ ValInt (n1 + 1)) (Val $ ValInt n2) e)).
  Proof.
    solve_pure_exec.
  Qed.

  #[global] Instance pure_block_immutable_nongenerative tag es vs :
    PureExec
      (to_vals es = Some vs)
      1
      (Block ImmutableNongenerative tag es)
      (Val $ ValBlock Nongenerative tag vs).
  Proof.
    intros <-%of_to_vals.
    apply nsteps_once, pure_base_step_pure_step.
    split; [solve_exec_safe | solve_exec_puredet].
  Qed.
  #[global] Instance pure_block_immutable_generative tag es vs :
    PureExec
      (to_vals es = Some vs)
      1
      (Block ImmutableGenerativeWeak tag es)
      (Val $ ValBlock (Generative None) tag vs).
  Proof.
    intros <-%of_to_vals.
    apply nsteps_once, pure_base_step_pure_step.
    split; [solve_exec_safe | solve_exec_puredet].
  Qed.

  #[global] Instance pure_match gen tag vs x_fb e_fb brs e :
    PureExec
      (eval_match tag (length vs) (SubjectBlock gen vs) x_fb e_fb brs = Some e)
      1
      (Match (Val $ ValBlock gen tag vs) x_fb e_fb brs)
      e.
  Proof.
    solve_pure_exec.
  Qed.

  #[global] Instance pure_get_tag gen tag vs :
    PureExec
      (0 < length vs)
      1
      (GetTag $ Val $ ValBlock gen tag vs)
      (Val $ ValNat tag).
  Proof.
    solve_pure_exec.
  Qed.

  #[global] Instance pure_get_size gen tag vs :
    PureExec
      (0 < length vs)
      1
      (GetSize $ Val $ ValBlock gen tag vs)
      (Val $ ValNat (length vs)).
  Proof.
    solve_pure_exec.
  Qed.

  #[global] Instance pure_get_field atm gen tag vs (fld : nat) v :
    PureExec
      (vs !! fld = Some v)
      1
      (GetField atm (Val $ ValBlock gen tag vs) (Val $ ValNat fld))
      (Val v).
  Proof.
    solve_pure_exec.
  Qed.
End pure_exec.
