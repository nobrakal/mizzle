From iris.proofmode Require Import base coq_tactics reduction proofmode.
From iris.proofmode Require Import intro_patterns.
From stdpp Require Import hlist.

From mizzle.lang Require Import instances.
From mizzle.lang Require Export semantics.

From mizzle.logic Require Import interp goal goal_proof.

(** * Goal-based tactics

    A thread is a focused hypothesis [Hp : focused p ks e]. Each tactic
    reads [e] and finds the redex [e_redex] in [fill K e_redex]. Pure
    steps decompose [e] via [reshape_expr] and apply the matching
    [focused_*_at] lemma, keeping [K] in the expression; effectful steps
    (and [g_for], [g_while], [g_fork]) instead fold [K] onto [ks] with
    [g_locate] and apply the context-free [focused_*] lemma (see "Locating
    a redex" below). Either way [Hp] is rebound and [simpl]ed, so chaining
    steps needs no [ks] bookkeeping. *)

(** Discharge a pure side-condition [φ] left by a pure-step lemma. Guarded
    against iris entailment goals (the [focused _ _ _ -∗ goal _]
    continuation): [simpl]-ing it on every step was the dominant cost. Also
    guard against [PureExec] premises — the [left]/[right] branches would
    otherwise prove one via the degenerate zero-step [nsteps_O], silently
    making the tactic a no-op. *)
Ltac solve_pure_φ :=
  lazymatch goal with
  | |- PureExec _ _ _ _ => fail
  | _ =>
    fast_done
    || (left; fast_done)
    || (right; fast_done)
    (* Guard the whole-term [simpl] against the iris continuation goal. *)
    || (lazymatch goal with
        | |- environments.envs_entails _ _ => fail
        | _ => simpl; reflexivity
        end)
    || (left; done)
    || (right; done)
    || done
  end.

(** Discharge the field lemmas' side-conditions ([0 ≤ fld],
    [vs !! Z.to_nat fld = Some v]). Guarded against the iris continuation. *)
Ltac g_field_sidecond :=
  lazymatch goal with
  | |- environments.envs_entails _ _ => fail
  | _ => first [ lia | reflexivity | done | (simpl; lia) | (simpl; reflexivity) ]
  end.

(** Decide [≉] on concrete closed values by reflection ([val_nonsimilar_dec]).
    Handles values differing *below* the top constructor (e.g. [2 :: l] vs
    [1 :: l]), which [inversion] on the witness cannot peel. Fails harmlessly
    when the values contain variables and [vm_compute] gets stuck. *)
Ltac decide_nonsimilar := apply (bool_decide_unpack _); vm_compute; exact I.

(** Discharge the [vl ≉ v1] side-condition of [focused_cas_fail]. [≉] is
    not definitionally [¬ ≈], so bridge via [val_similar_or_nonsimilar]: close
    it from a [¬ (_ ≈ _)] hypothesis or a top-constructor mismatch, else fall
    back to [decide_nonsimilar]. Guarded against the iris continuation. *)
Ltac solve_nonsimilar :=
  lazymatch goal with
  | |- environments.envs_entails _ _ => fail
  | |- ?a ≉ ?b =>
      solve
        [ assumption
        | match goal with
          | H : ¬ (a ≈ b) |- _ =>
              destruct (val_similar_or_nonsimilar a b) as [?Hs | ?Hns];
              [ exfalso; exact (H Hs) | exact Hns ]
          end
        | destruct (val_similar_or_nonsimilar a b) as [?Hs | ?Hns];
          (* [inversion] refutes a top-constructor mismatch; [; congruence]
             also closes [#x ≉ #y] from a location hypothesis [x ≠ y]. *)
          [ solve [ inversion Hs | (inversion Hs; congruence) ] | exact Hns ]
        | decide_nonsimilar ]
  (* Dual shape, when a helper threads a [¬ (_ ≈ _)] premise. *)
  | |- ¬ (?a ≈ ?b) =>
      solve [ assumption | decide_nonsimilar
            | intros ?Hs; inversion Hs; congruence ]
  end.

(** Extract [(ks, e)] from [Hp : focused _ ks e] and call [tac ks e];
    default [ks] to [[]] when the outer [fill _] has collapsed. *)
Ltac with_focused_ks_e Hp tac :=
  let typ := iTypeOf Hp in
  lazymatch typ with
  | Some (_, running _ (fill ?ks ?e)) => tac ks e
  | Some (_, running _ ?e) => tac (@nil ectxi) e
  | Some (_, ?P) => fail "with_focused_ks_e:" Hp "has type" P ", expected a [focused]"
  | None => fail "with_focused_ks_e: hypothesis" Hp "not found"
  end.

Ltac mk_spec_1 Hp := constr:(Hp).
Ltac mk_spec_2 Hp Hl := constr:((Hp ++ " " ++ Hl)%string).
Ltac mk_intro_2 H1 H2 := constr:((H1 ++ " " ++ H2)%string).

(** ** Focusing

    [g_focus efoc Hp] is the focused-mode analog of [wp_bind]. Given
    [Hp : focused p ks e], it decomposes [e] into [fill K e'] with [e']
    unifying [efoc], folds [K] into [ks] via [focused_bind_l], and rebinds
    [Hp : focused p (K ++ ks) e']. *)
Tactic Notation "g_focus" open_constr(efoc) constr(Hp) :=
  iStartProof;
  with_focused_ks_e Hp ltac:(fun ks e =>
    let e := eval simpl in e in
    first
      [ reshape_expr e ltac:(fun K e' =>
          unify e' efoc;
          lazymatch eval hnf in K with
          | [] => idtac
          | _ =>
            iDestruct (focused_bind_l K _ ks with Hp) as Hp
          end)
      | fail 1 "g_focus: cannot find" efoc "in" e ]).

(** ** Locating a redex

    [g_locate Hp is_redex on_miss] finds the first redex on the spine of
    [Hp : focused p ks e] accepted by [is_redex] (an Ltac predicate on the
    candidate, failing to reject it), folds its context onto [ks] via
    [focused_bind_l] and rebinds [Hp] at the bare redex. [e] is tried as-is
    first and [simpl]-ed second. Only when no candidate exists does
    [on_miss e] run, to produce the diagnostic.

    Every step tactic below is [g_locate] followed by the context-free
    [focused_*] lemma. Keeping the application outside the search means a
    failure there — a missing or ill-shaped hypothesis, a side condition the
    automation cannot close — surfaces as its own error and is never
    reported as a missing redex. *)
Ltac g_locate_in ks e Hp is_redex :=
  reshape_expr e ltac:(fun K e' =>
    is_redex e';
    lazymatch eval hnf in K with
    | [] => idtac
    | _ => iDestruct (focused_bind_l K _ ks with Hp) as Hp
    end).
Ltac g_locate Hp is_redex on_miss :=
  with_focused_ks_e Hp ltac:(fun ks e =>
    first
      [ g_locate_in ks e Hp is_redex
      | let e := eval simpl in e in g_locate_in ks e Hp is_redex
      | let e := eval simpl in e in on_miss e ]).

(** ** The shared miss diagnostic

    [is_step e'] accepts exactly the expressions that are a redex of the
    semantics: every operand the step reads is a [Val]. [all_vals] is its
    helper for the field list of a [Block]. *)
Ltac all_vals es :=
  lazymatch es with
  | nil => idtac
  | cons (Val _) ?rest => all_vals rest
  end.
Ltac is_step e' :=
  lazymatch e' with
  | App (Val _) (Val _) => idtac
  | Rec _ _ _ => idtac
  | Let _ (Val _) _ => idtac
  | Seq (Val _) _ => idtac
  | If (Val _) _ _ => idtac
  | Unop _ (Val _) => idtac
  | Binop _ (Val _) (Val _) => idtac
  | Equal (Val _) (Val _) => idtac
  | While _ _ => idtac
  | For (Val _) (Val _) _ => idtac
  | Match (Val _) _ _ _ => idtac
  | Block _ _ ?es => all_vals es
  | GetField _ (Val _) (Val _) => idtac
  | SetField _ (Val _) (Val _) (Val _) => idtac
  | CAS (Val _) (Val _) (Val _) => idtac
  | Xchg (Val _) (Val _) => idtac
  | FAA (Val _) (Val _) => idtac
  | Fork _ => idtac
  end.

(** [g_miss name strict loose e] is what every step tactic reports when
    [g_locate] finds nothing. [strict] is the redex the tactic fires on, with
    holes; [loose] is the same head with every operand a hole. The report
    says one of three things, in this order:
    - the strict shape occurs in [e] but is not the next redex: the spine
      (right-to-left) reduces some other redex first, which is named;
    - the loose shape occurs: an operand is still an expression;
    - neither occurs. *)
Ltac g_miss name strict loose e :=
  first
    [ match e with
      | context [?t] =>
        unify t strict;
        first
          [ let next := constr:(ltac:(reshape_expr e ltac:(fun _ e' => is_step e'; exact e'))) in
            fail 4 name ":" t "is present but not the next redex — the spine reduces" next
                   "first (right-to-left); step it, then retry"
          | fail 4 name ":" t "is present but not on the evaluation spine of" e ]
      end
    | match e with
      | context [?t] =>
        unify t loose;
        fail 3 name ": an operand of" t "is not yet a value — reduce it first (g_args)"
      end
    | fail 2 name ": no" loose "in" e ].

(** After a spec application: advance the continuation goal, and name any
    side condition the automation left open instead of failing obscurely. *)
Ltac g_continue intros Hp :=
  lazymatch goal with
  | |- environments.envs_entails _ _ => iIntros intros; iEval (simpl) in Hp
  | |- ?G => fail 1 "side condition not discharged automatically:" G
  end.

(** ** Integer normalization

    [g_znorm Hp] replaces every closed [ValInt z] whose [z] is not yet a
    literal but computes to one (e.g. [(20 - 1)%Z]) by its value. Open terms
    (mentioning variables) are left alone. *)
Tactic Notation "g_znorm" constr(Hp) :=
  iStartProof;
  repeat
    with_focused_ks_e Hp ltac:(fun ks e =>
      match e with
      | context [ValInt ?z] =>
        lazymatch z with
        | Z0 => fail
        | Zpos _ => fail
        | Zneg _ => fail
        | _ =>
          let z' := eval vm_compute in z in
          lazymatch z' with
          | Z0 => idtac
          | Zpos _ => idtac
          | Zneg _ => idtac
          end;
          replace z with z' by lia
        end
      end).

(** ** Pure steps *)

Tactic Notation "g_pure" open_constr(efoc) constr(Hp) :=
  iStartProof;
  with_focused_ks_e Hp ltac:(fun ks e =>
    let e := eval simpl in e in
    first
      [ reshape_expr e ltac:(fun K e' =>
          unify e' efoc;
          let spec := mk_spec_1 Hp in
          iApply (ITrm (focused_pure_step_at _ K _ ks e' _ _ _) hnil spec);
          try (first [tc_solve | solve_pure_φ]);
          try (iIntros Hp; iSimpl in Hp))
      | (* Diagnose the two common misses (per lin012): the focused
           expression is already a value, or a redex of the wanted head is
           present but its operands are not values yet. *)
        lazymatch e with
        | Val _ =>
          fail 1 "g_pure: cannot find" efoc "-- the focused expression" e
               "is a value left under a folded context by a hand-applied lemma;"
               "iEval (simpl) in the hypothesis refolds it"
        | _ =>
          first
            [ let next := constr:(ltac:(reshape_expr e ltac:(fun _ e' => is_step e'; exact e'))) in
              fail 2 "g_pure: cannot find" efoc "in" e "-- the spine reduces" next
                     "first (right-to-left); step it, or reduce its operands with g_args"
            | fail 2 "g_pure: cannot find" efoc "in" e
                     "-- if the leading redex has this head, its operands are not yet values" ]
        end ]).

(** Reduce a leading pure block-projection [e.<proj>] — a [GetField] on a literal
    [ValBlock] base — to a value, so a heap/call tactic reaches
    its redex. The base is pinned to [ValBlock] so only pure projections step,
    never a heap [GetField]; a no-op otherwise. Prepended by [g_get_field]/[g_set_field]/
    [g_call]. *)
Ltac g_reduce_proj Hp := repeat (g_pure (GetField _ (Val (ValBlock _ _ _)) (Val _)) Hp).

(** Pure-step shorthands. [g_rec] uses the direct [focused_rec_at] lemma
    rather than letting [tc_solve] search for the [PureExec] instance. *)
Tactic Notation "g_rec" constr(Hp) :=
  iStartProof;
  with_focused_ks_e Hp ltac:(fun ks e =>
    let e := eval simpl in e in
    first
      [ reshape_expr e ltac:(fun K e' =>
          lazymatch e' with
          | Rec _ _ _ =>
            let spec := mk_spec_1 Hp in
            iApply (ITrm (focused_rec_at _ K _ ks _ _ _) hnil spec);
            try (iIntros Hp; iSimpl in Hp)
          end)
      | fail 1 "g_rec: no Rec redex in" e ]).
Tactic Notation "g_let" constr(Hp) := g_pure (Let _ (Val _) _) Hp.
(** Beta-reduction of [App (Val (ValRecs _ _)) (Val _)]. The common
    single-recursive case ([ValRec]/[ValFun]) is stepped by [focused_beta_at],
    which carries the [PureExec] instance — avoiding the loop-prone
    [AsValRecs] search (the dominant cost of [g_call]). For a genuinely
    mutually-recursive [ValRecs i recs] (rare) it fails to unify and we fall
    back to the generic pure-step path, first [assert]ing the
    [ValRec_as_ValRec] / [as_ValRecs'_as_ValRecs] instances (from
    [lang/instances]) to dodge the [AsValRecs'] cycle. *)
Tactic Notation "g_call" constr(Hp) :=
  iStartProof;
  (* Reduce an argument-position projection first, so the redex is reachable. *)
  g_reduce_proj Hp;
  with_focused_ks_e Hp ltac:(fun ks e =>
    let e := eval simpl in e in
    first
      [ reshape_expr e ltac:(fun K e' =>
          lazymatch e' with
          | App (Val (ValRecs _ _)) (Val _) =>
            let spec := mk_spec_1 Hp in
            first
              [ iApply (ITrm (focused_beta_at _ K _ ks _ _ _ _) hnil spec)
              | let H1 := fresh in assert (H1 := ValRec_as_ValRec);
                let H2 := fresh in assert (H2 := as_ValRecs'_as_ValRecs);
                iApply (ITrm (focused_pure_step_at _ K _ ks e' _ _ _) hnil spec);
                (try (first [tc_solve | solve_pure_φ]));
                clear H1 H2 ];
            try (iIntros Hp; iSimpl in Hp)
          end)
      | (* On failure, report an application argument that is not yet a value. *)
        reshape_expr e ltac:(fun _ e' =>
          lazymatch e' with
          | App (Val _) ?arg =>
            lazymatch arg with
            | Val _ => fail
            | _ => fail 1 "g_call: the call argument is not a value:" arg
            end
          end)
      | fail 1 "g_call: no application redex in" e ]).

(** Multi-arg call expansion: each application after the first needs a
    [g_rec] before [g_call]. [g_callN H] does the N nested beta steps. *)
Tactic Notation "g_call2" constr(Hp) :=
  g_call Hp; g_rec Hp; g_call Hp.
Tactic Notation "g_call3" constr(Hp) :=
  g_call Hp; g_rec Hp; g_call Hp; g_rec Hp; g_call Hp.
Tactic Notation "g_call4" constr(Hp) :=
  g_call Hp; g_rec Hp; g_call Hp; g_rec Hp; g_call Hp; g_rec Hp; g_call Hp.

Tactic Notation "g_if" constr(Hp) := g_pure (If (Val _) _ _) Hp.
Tactic Notation "g_if_true" constr(Hp) :=
  g_pure (If (Val (ValBool true)) _ _) Hp.
Tactic Notation "g_if_false" constr(Hp) :=
  g_pure (If (Val (ValBool false)) _ _) Hp.

(** A [Unop]/[Binop] is a redex only when its operands are values. *)
Tactic Notation "g_unop" constr(Hp) := g_pure (Unop _ (Val _)) Hp.
Tactic Notation "g_binop" constr(Hp) := g_pure (Binop _ (Val _) (Val _)) Hp.
Tactic Notation "g_op" constr(Hp) := first [g_unop Hp | g_binop Hp].

(** Reduce a call's arguments to literals. A tactic wanting a value (an
    array access, [g_let], a spec lemma) matches only once every argument is
    a single [ValInt z], and reaching that is one conceptual step, not a
    count of operators: [repeat g_binop] drives the arithmetic to a fixpoint
    and [g_znorm] then computes the closed literals. *)
Tactic Notation "g_args" constr(Hp) := repeat g_binop Hp; g_znorm Hp.

Tactic Notation "g_equal" constr(Hp) :=
  g_pure (Equal (Val _) (Val _)) Hp.
(** A [Match] is a redex only once its scrutinee is a value; pinning it to
    [Val _] also prunes the search (a wildcard [g_pure (Match _ _ _ _)] runs
    [PureExec] at every match decomposition and can hit [Coq: Timeout!]). For
    extra pinning pass the scrutinee's constructor, e.g.
    [g_pure (Match (‘Some( _ ))%V _ _ _) Hp]. *)
Tactic Notation "g_match" constr(Hp) := g_pure (Match (Val _) _ _ _) Hp.

(** A [Seq e1 e2] is a redex only once [e1] is a value; pinning the left to
    [Val _] avoids unifying against a still-reducible outer [Seq] and hanging
    the [PureExec] search. *)
Tactic Notation "g_seq" constr(Hp) := g_pure (Seq (Val _) _) Hp.

(** Reduce a leading applied constructor [Block _ _ [e1;…;en]] (e.g. [‘Some(v)],
    [x :: xs], a tuple) to its value. A [Block] is a redex only once all fields
    are values, so [all_vals] guards the step: [reshape_expr] fires only on a
    block whose fields are syntactically [Val _], reducing nested constructors
    inside-out and never running [PureExec] on a non-redex. [g_block]
    repeats to a fixpoint; a no-op when the expression is not a block. *)
Ltac g_block_step Hp :=
  with_focused_ks_e Hp ltac:(fun ks e =>
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      lazymatch e' with
      | Block _ _ ?es =>
        all_vals es;
        let spec := mk_spec_1 Hp in
        iApply (ITrm (focused_pure_step_at _ K _ ks e' _ _ _) hnil spec);
        try (first [tc_solve | solve_pure_φ]);
        try (iIntros Hp; iSimpl in Hp)
      end)).
Tactic Notation "g_block" constr(Hp) :=
  iStartProof; repeat (g_block_step Hp).

(** [g_tuple] is [g_block] restricted to tuples — an unlabelled [(a, b, …)].
    Use it over [g_block] to leave labelled constructors alone, or for intent. *)
Ltac g_tuple_step Hp :=
  with_focused_ks_e Hp ltac:(fun ks e =>
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      lazymatch e' with
      | Tuple ?es =>
        all_vals es;
        let spec := mk_spec_1 Hp in
        iApply (ITrm (focused_pure_step_at _ K _ ks e' _ _ _) hnil spec);
        try (first [tc_solve | solve_pure_φ]);
        try (iIntros Hp; iSimpl in Hp)
      end)).
Tactic Notation "g_tuple" constr(Hp) :=
  iStartProof; repeat (g_tuple_step Hp).

Tactic Notation "g_for" constr(Hp) :=
  iStartProof;
  g_locate Hp
    ltac:(fun e' => lazymatch e' with For (Val (ValInt _)) (Val (ValInt _)) _ => idtac end)
    ltac:(fun e => g_miss "g_for" open_constr:(For (Val (ValInt _)) (Val (ValInt _)) _)
                          open_constr:(For _ _ _) e);
  let spec := mk_spec_1 Hp in
  first
    [ with_focused_ks_e Hp ltac:(fun ks _ => iApply (ITrm (focused_for_step _ _ ks _ _ _) hnil spec));
      [ first [lia | simpl; lia] | try (iIntros Hp; iSimpl in Hp) ]
    | with_focused_ks_e Hp ltac:(fun ks _ => iApply (ITrm (focused_for_done _ _ ks _ _ _) hnil spec));
      [ first [lia | simpl; lia] | try (iIntros Hp; iSimpl in Hp) ]
    | with_focused_ks_e Hp ltac:(fun _ e =>
        fail 1 "g_for: lia can decide neither lo < n (step) nor n ≤ lo (done) for" e) ].

(** [g_while Hp] unfolds one iteration of the leading [While e0 e1] into
    [if: e0 then (e1 ;; While e0 e1) else ()]. *)
Tactic Notation "g_while" constr(Hp) :=
  iStartProof;
  g_locate Hp
    ltac:(fun e' => lazymatch e' with While _ _ => idtac end)
    ltac:(fun e => g_miss "g_while" open_constr:(While _ _) open_constr:(While _ _) e);
  let spec := mk_spec_1 Hp in
  with_focused_ks_e Hp ltac:(fun ks _ => iApply (ITrm (focused_while _ _ ks _ _) hnil spec));
  try (iIntros Hp; iSimpl in Hp).

(** ** Effectful steps

    Each tactic is [g_locate] then the context-free [focused_*] lemma on the
    bare redex; a miss is reported by [g_miss]. *)

Tactic Notation "g_alloc" constr(Hp) constr(Hl) :=
  iStartProof;
  g_locate Hp
    ltac:(fun e' => lazymatch e' with (ref _)%E => idtac end)
    ltac:(fun e => g_miss "g_alloc" open_constr:((ref (Val _))%E) open_constr:((ref _)%E) e);
  let spec := mk_spec_1 Hp in
  let intros := mk_intro_2 Hl Hp in
  with_focused_ks_e Hp ltac:(fun ks _ => iApply (ITrm (focused_alloc _ _ ks _) hnil spec));
  iIntros (?) intros;
  iEval (simpl) in Hp.

Ltac g_locate_get_field Hp name :=
  g_locate Hp
    ltac:(fun e' => lazymatch e' with GetField _ (Val _) (Val _) => idtac end)
    ltac:(fun e => g_miss name open_constr:(GetField _ (Val _) (Val _)) open_constr:(GetField _ _ _) e).
Ltac g_locate_set_field Hp name :=
  g_locate Hp
    ltac:(fun e' => lazymatch e' with SetField _ (Val _) (Val _) (Val _) => idtac end)
    ltac:(fun e => g_miss name open_constr:(SetField _ (Val _) (Val _) (Val _)) open_constr:(SetField _ _ _ _) e).

Tactic Notation "g_get_field" constr(Hp) constr(Hl) :=
  iStartProof;
  g_reduce_proj Hp;
  g_locate_get_field Hp "g_get_field";
  let spec := mk_spec_2 Hp Hl in
  let intros := mk_intro_2 Hl Hp in
  with_focused_ks_e Hp ltac:(fun ks _ => iApply (ITrm (focused_get_field _ _ ks _ _ _ _ _ _) hnil spec));
  try g_field_sidecond;
  g_continue intros Hp.

Tactic Notation "g_set_field" constr(Hp) constr(Hl) :=
  iStartProof;
  g_reduce_proj Hp;
  g_locate_set_field Hp "g_set_field";
  let spec := mk_spec_2 Hp Hl in
  let intros := mk_intro_2 Hl Hp in
  with_focused_ks_e Hp ltac:(fun ks _ => iApply (ITrm (focused_set_field _ _ ks _ _ _ _ _ _) hnil spec));
  try g_field_sidecond;
  g_continue intros Hp.

(** Reduce a CAS's location descriptor to a value. A field descriptor
    [(#l).[fld]] is a [Block] over base and offset that must reduce to a [Val]
    before [focused_cas_*] sees [CAS (Val _) (Val _) (Val _)]. When the base
    is itself a pure block-projection [e.<proj>] on a literal pair, that inner
    projection must reduce first, so alternate the two reductions, pinning the
    GetField's base to [ValBlock] to step only pure projections. A no-op when
    the descriptor is already a value. *)
Ltac g_reduce_cas_descr Hp :=
  repeat (first
    [ g_pure (GetField _ (Val (ValBlock _ _ _)) (Val _)) Hp
    | g_pure (Block _ _ _) Hp ]).

Ltac g_locate_cas Hp name :=
  g_locate Hp
    ltac:(fun e' => lazymatch e' with CAS (Val _) (Val _) (Val _) => idtac end)
    ltac:(fun e => g_miss name open_constr:(CAS (Val _) (Val _) (Val _)) open_constr:(CAS _ _ _) e).

Tactic Notation "g_cas_prim_succ" constr(Hp) constr(Hl) :=
  iStartProof;
  g_reduce_cas_descr Hp;
  g_locate_cas Hp "g_cas_prim_succ";
  let spec := mk_spec_2 Hp Hl in
  let intros := mk_intro_2 Hl Hp in
  with_focused_ks_e Hp ltac:(fun ks _ => iApply (ITrm (focused_cas_succ _ _ ks _ _ _ _ _ _) hnil spec));
  try g_field_sidecond;
  g_continue intros Hp.

(** Step a failing CAS. [focused_cas_fail] carries an extra user-supplied
    [vl ≉ v1] premise: [g_field_sidecond] closes the bound/lookup,
    [solve_nonsimilar] closes [≉] when possible, and the continuation is
    advanced; an unclosed [≉] is left as a residual goal. *)
Tactic Notation "g_cas_prim_fail" constr(Hp) constr(Hl) :=
  iStartProof;
  g_reduce_cas_descr Hp;
  g_locate_cas Hp "g_cas_prim_fail";
  let spec := mk_spec_2 Hp Hl in
  let intros := mk_intro_2 Hl Hp in
  with_focused_ks_e Hp ltac:(fun ks _ => iApply (ITrm (focused_cas_fail _ _ ks _ _ _ _ _ _ _) hnil spec));
  try g_field_sidecond;
  try solve_nonsimilar;
  try (lazymatch goal with
       | |- environments.envs_entails _ _ =>
           iIntros intros; iEval (simpl) in Hp
       end).

(** ** Header-aware single-cell effectful steps (framework-internal)

    [g_*_cell Hp Hh Hl] step thread [Hp] using the persistent header
    [Hh : l ↦ₕ{dqh} hdr] and a single cell [Hl : (l +ₗ fld) ↦ v], certifying
    [wf_access] from the header. They are the building blocks of the
    [stdlib] specs whose representation keeps the header separate from the
    cells ([array], [trace], [ivar]); benchmark proofs never call them and
    go through the [g_array_*] tactics instead. *)

Tactic Notation "g_get_field_cell" constr(Hp) constr(Hh) constr(Hl) :=
  iStartProof;
  g_locate_get_field Hp "g_get_field_cell";
  let spec := constr:((Hp ++ " " ++ Hh ++ " " ++ Hl)%string) in
  let intros := constr:((Hh ++ " " ++ Hl ++ " " ++ Hp)%string) in
  with_focused_ks_e Hp ltac:(fun ks _ => iApply (ITrm (focused_get_field_cell _ _ ks _ _ _ _ _ _ _) hnil spec));
  try g_field_sidecond;
  g_continue intros Hp.

Tactic Notation "g_set_field_cell" constr(Hp) constr(Hh) constr(Hl) :=
  iStartProof;
  g_locate_set_field Hp "g_set_field_cell";
  let spec := constr:((Hp ++ " " ++ Hh ++ " " ++ Hl)%string) in
  let intros := constr:((Hh ++ " " ++ Hl ++ " " ++ Hp)%string) in
  with_focused_ks_e Hp ltac:(fun ks _ => iApply (ITrm (focused_set_field_cell _ _ ks _ _ _ _ _ _ _) hnil spec));
  try g_field_sidecond;
  g_continue intros Hp.

Tactic Notation "g_cas_succ_cell" constr(Hp) constr(Hh) constr(Hl) :=
  iStartProof;
  g_reduce_cas_descr Hp;
  g_locate_cas Hp "g_cas_succ_cell";
  let spec := constr:((Hp ++ " " ++ Hh ++ " " ++ Hl)%string) in
  let intros := constr:((Hh ++ " " ++ Hl ++ " " ++ Hp)%string) in
  with_focused_ks_e Hp ltac:(fun ks _ => iApply (ITrm (focused_cas_succ_cell _ _ ks _ _ _ _ _ _ _) hnil spec));
  try g_field_sidecond;
  g_continue intros Hp.

Tactic Notation "g_cas_fail_cell" constr(Hp) constr(Hh) constr(Hl) :=
  iStartProof;
  g_reduce_cas_descr Hp;
  g_locate_cas Hp "g_cas_fail_cell";
  let spec := constr:((Hp ++ " " ++ Hh ++ " " ++ Hl)%string) in
  let intros := constr:((Hh ++ " " ++ Hl ++ " " ++ Hp)%string) in
  with_focused_ks_e Hp ltac:(fun ks _ => iApply (ITrm (focused_cas_fail_cell _ _ ks _ _ _ _ _ _ _ _) hnil spec));
  try g_field_sidecond;
  g_continue intros Hp.

(** [g_fork Hp Hpnew Hloc] — the spawned thread arrives as a fresh
    [focused _ [] e_forked] under [Hpnew], its initial local resource under
    [Hloc] (seeded to [ValUnit]); [Hp] is rebound at [Val ValUnit]. *)
Tactic Notation "g_fork" constr(Hp) constr(Hpnew) constr(Hloc) :=
  iStartProof;
  g_locate Hp
    ltac:(fun e' => lazymatch e' with Fork _ => idtac end)
    ltac:(fun e => g_miss "g_fork" open_constr:(Fork _) open_constr:(Fork _) e);
  let spec := mk_spec_1 Hp in
  let intros1 := mk_intro_2 Hloc Hpnew in
  let intros := mk_intro_2 intros1 Hp in
  with_focused_ks_e Hp ltac:(fun ks _ => iApply (ITrm (focused_fork _ _ ks _ ValUnit) hnil spec));
  first done;
  iIntros (?) intros;
  iEval (simpl) in Hp.

(** ** Generic loop marching

    [focused_loop_prefix] marches a thread from iteration [lo] to [mid] of
    [For #lo #n body] under an invariant [I], parking it at [For #mid #n body]
    — so a proof can march up to the iteration where it races. The
    per-iteration obligation: given [I i] and the thread at [App body #i],
    drive the body to [()] and re-establish [I (i+1)]. It is a persistent
    hypothesis, so proving it under [iModIntro] keeps every persistent fact
    of the ambient context (a □ array header) in scope; only spatial
    resources the body needs have to travel inside [I].

    [focused_loop_inv] is the [mid = n] instance, running to completion. Both
    subsume the per-shape induction lemmas ([focused_set_loop] etc.). *)
Section loop.
Context `{seqlogGS Σ}.

(** [[card]] *)
Lemma focused_loop_prefix E p (I : Z → iProp Σ) (lo mid n : Z) (body : expr) ks :
  (lo <= mid <= n)%Z →
  □ (∀ (i:Z) (ks':list ectxi) (_ : (lo <= i < mid)%Z),
       I i -∗
       focused p ks' (App body (Val (ValInt i))) -∗
       (I (i+1)%Z -∗ focused p ks' (Val ValUnit) -∗ goal E) -∗
       goal E) -∗
  I lo -∗
  focused p ks (For (Val (ValInt lo)) (Val (ValInt n)) body) -∗
  (I mid -∗ focused p ks (For (Val (ValInt mid)) (Val (ValInt n)) body) -∗ goal E) -∗
  goal E.
Proof.
  intros Hle.
  remember (Z.to_nat (mid - lo)) as d eqn:Hd.
  revert lo Hd Hle.
  induction d as [|d IH]; intros lo Hd Hle.
  - assert (lo = mid) as -> by lia.
    iIntros "#Hbody HI Hf Hcont". iApply ("Hcont" with "HI Hf").
  - iIntros "#Hbody HI Hf Hcont".
    iApply (focused_for_step with "Hf"); first lia.
    iIntros "Hf".
    iDestruct (focused_bind_l [CtxLet BAnon _] with "Hf") as "Hf".
    assert (Hi : (lo <= lo < mid)%Z) by lia.
    iApply ("Hbody" $! lo _ Hi with "HI Hf").
    iIntros "HI Hf".
    iEval (rewrite -focused_bind) in "Hf".
    g_let "Hf".
    iApply (IH (lo+1)%Z with "[] HI Hf Hcont"); try lia.
    iModIntro. iIntros (i ks' Hi').
    assert (Hi'' : (lo <= i < mid)%Z) by lia.
    iApply ("Hbody" $! i ks' Hi'').
Qed.

(** [[card]] *)
Lemma focused_loop_inv E p (I : Z → iProp Σ) (lo n : Z) (body : expr) ks :
  (lo <= n)%Z →
  □ (∀ (i:Z) (ks':list ectxi) (_ : (lo <= i < n)%Z),
       I i -∗
       focused p ks' (App body (Val (ValInt i))) -∗
       (I (i+1)%Z -∗ focused p ks' (Val ValUnit) -∗ goal E) -∗
       goal E) -∗
  I lo -∗
  focused p ks (For (Val (ValInt lo)) (Val (ValInt n)) body) -∗
  (I n -∗ focused p ks (Val ValUnit) -∗ goal E) -∗
  goal E.
Proof.
  intros Hle.
  iIntros "#Hbody HI Hf Hcont".
  iApply (focused_loop_prefix E p I lo n n body ks with "Hbody HI Hf"); first lia.
  iIntros "HI Hf".
  iApply (focused_for_done with "Hf"); first lia.
  iIntros "Hf". iApply ("Hcont" with "HI Hf").
Qed.

End loop.
