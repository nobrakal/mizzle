From stdpp Require Import base list.
From mizzle.lang Require Import semantics.

(* [split_block es]: find the rightmost non-value in [es]. Returns
   [Some (prefix, hole, vs)] with [es = prefix ++ hole :: of_vals vs] and
   [to_val hole = None]; [None] if every entry is a value. Block uses
   right-to-left evaluation order. *)
Fixpoint split_block (es : list expr) : option (list expr * expr * list val) :=
  match es with
  | [] => None
  | e :: es' =>
      match split_block es' with
      | Some (pre, hole, suf) => Some (e :: pre, hole, suf)
      | None =>
          match to_val e, to_vals es' with
          | None, Some vs => Some ([], e, vs)
          | _, _ => None
          end
      end
  end.

(* One step of decomposition: peel a single evaluation-context frame off
   the top of [e]. Returns [None] when [e] is a value, a head redex, or
   otherwise stuck at the surface. *)
Definition decompose_step (e : expr) : option (ectxi * expr) :=
  match e with
  | Val _ | Var _ | Rec _ _ _ | While _ _ | GetLocal | Fork _ =>
      None
  | App e1 e2 =>
      match to_val e2 with
      | None => Some (CtxApp2 e1, e2)
      | Some v2 =>
          match to_val e1 with
          | None => Some (CtxApp1 v2, e1)
          | Some _ => None
          end
      end
  | Let x e1 e2 =>
      match to_val e1 with
      | None => Some (CtxLet x e2, e1)
      | Some _ => None
      end
  | Unop op e1 =>
      match to_val e1 with
      | None => Some (CtxUnop op, e1)
      | Some _ => None
      end
  | Binop op e1 e2 =>
      match to_val e2 with
      | None => Some (CtxBinop2 op e1, e2)
      | Some v2 =>
          match to_val e1 with
          | None => Some (CtxBinop1 op v2, e1)
          | Some _ => None
          end
      end
  | Equal e1 e2 =>
      match to_val e2 with
      | None => Some (CtxEqual2 e1, e2)
      | Some v2 =>
          match to_val e1 with
          | None => Some (CtxEqual1 v2, e1)
          | Some _ => None
          end
      end
  | If e0 e1 e2 =>
      match to_val e0 with
      | None => Some (CtxIf e1 e2, e0)
      | Some _ => None
      end
  | For e1 e2 e3 =>
      match to_val e1 with
      | None => Some (CtxFor1 e2 e3, e1)
      | Some v1 =>
          match to_val e2 with
          | None => Some (CtxFor2 v1 e3, e2)
          | Some _ => None
          end
      end
  | Alloc e1 e2 =>
      match to_val e2 with
      | None => Some (CtxAlloc2 e1, e2)
      | Some v2 =>
          match to_val e1 with
          | None => Some (CtxAlloc1 v2, e1)
          | Some _ => None
          end
      end
  | Block mut tag es =>
      match split_block es with
      | Some (pre, hole, suf) => Some (CtxBlock mut tag pre suf, hole)
      | None => None
      end
  | Match e0 x e1 brs =>
      match to_val e0 with
      | None => Some (CtxMatch x e1 brs, e0)
      | Some _ => None
      end
  | GetTag e1 =>
      match to_val e1 with
      | None => Some (CtxGetTag, e1)
      | Some _ => None
      end
  | GetSize e1 =>
      match to_val e1 with
      | None => Some (CtxGetSize, e1)
      | Some _ => None
      end
  | GetField atm e1 e2 =>
      match to_val e2 with
      | None => Some (CtxGetField2 atm e1, e2)
      | Some v2 =>
          match to_val e1 with
          | None => Some (CtxGetField1 atm v2, e1)
          | Some _ => None
          end
      end
  | SetField atm e1 e2 e3 =>
      match to_val e3 with
      | None => Some (CtxSetField3 atm e1 e2, e3)
      | Some v3 =>
          match to_val e2 with
          | None => Some (CtxSetField2 atm e1 v3, e2)
          | Some v2 =>
              match to_val e1 with
              | None => Some (CtxSetField1 atm v2 v3, e1)
              | Some _ => None
              end
          end
      end
  | Xchg e1 e2 =>
      match to_val e2 with
      | None => Some (CtxXchg2 e1, e2)
      | Some v2 =>
          match to_val e1 with
          | None => Some (CtxXchg1 v2, e1)
          | Some _ => None
          end
      end
  | CAS e0 e1 e2 =>
      match to_val e2 with
      | None => Some (CtxCAS2 e0 e1, e2)
      | Some v2 =>
          match to_val e1 with
          | None => Some (CtxCAS1 e0 v2, e1)
          | Some v1 =>
              match to_val e0 with
              | None => Some (CtxCAS0 v1 v2, e0)
              | Some _ => None
              end
          end
      end
  | FAA e1 e2 =>
      match to_val e2 with
      | None => Some (CtxFAA2 e1, e2)
      | Some v2 =>
          match to_val e1 with
          | None => Some (CtxFAA1 v2, e1)
          | Some _ => None
          end
      end
  | SetLocal e1 =>
      match to_val e1 with
      | None => Some (CtxSetLocal, e1)
      | Some _ => None
      end
  | Emit e1 =>
      match to_val e1 with
      | None => Some (CtxEmit, e1)
      | Some _ => None
      end
  end.

(* Fuelled iteration of [decompose_step]. Returns [(K, r)] with
   [fill K r = e]; [r] is the deepest sub-expression we can reach (i.e.
   [decompose_step r = None]) provided [n] is large enough — using
   [expr_size e] is always sufficient. *)
Fixpoint decompose_fuel (n : nat) (e : expr) : ectx * expr :=
  match n with
  | 0 => ([], e)
  | S n' =>
      match decompose_step e with
      | None => ([], e)
      | Some (k, e') =>
          let '(K, r) := decompose_fuel n' e' in
          (K ++ [k], r)
      end
  end.

(* A crude size measure on expressions; only used to bound fuel. *)
Fixpoint expr_size (e : expr) : nat :=
  match e with
  | Val _ | Var _ | GetLocal => 1
  | Rec _ _ e1 | Unop _ e1 | GetTag e1 | GetSize e1 | Fork e1 | SetLocal e1
  | Emit e1 =>
      S (expr_size e1)
  | App e1 e2 | Let _ e1 e2 | Binop _ e1 e2 | Equal e1 e2 | While e1 e2
  | Alloc e1 e2 | Xchg e1 e2 | FAA e1 e2 =>
      S (expr_size e1 + expr_size e2)
  | GetField _ e1 e2 =>
      S (expr_size e1 + expr_size e2)
  | If e0 e1 e2 | For e0 e1 e2 | CAS e0 e1 e2 =>
      S (expr_size e0 + expr_size e1 + expr_size e2)
  | SetField _ e0 e1 e2 =>
      S (expr_size e0 + expr_size e1 + expr_size e2)
  | Block _ _ es =>
      S (list_sum (map expr_size es))
  | Match e0 _ e1 brs =>
      S (expr_size e0 + expr_size e1 + list_sum (map (fun b => expr_size b.2) brs))
  end.

Definition decompose (e : expr) : ectx * expr :=
  decompose_fuel (expr_size e) e.

(* ---------- Correctness ---------- *)

Lemma fill_snoc K k e :
  fill (K ++ [k]) e = filli k (fill K e).
Proof. unfold fill. by rewrite foldl_app. Qed.

Lemma split_block_sound es pre hole suf :
  split_block es = Some (pre, hole, suf) →
  es = pre ++ hole :: of_vals suf ∧ to_val hole = None.
Proof.
  revert pre hole suf.
  induction es as [|e' es' IH]; intros pre hole suf; simpl; first done.
  destruct (split_block es') as [[[pre' hole'] suf']|] eqn:Hrec.
  - intros [= <- <- <-]. destruct (IH pre' hole' suf' eq_refl) as [-> Hnv].
    split; [done|done].
  - destruct (to_val e') as [|] eqn:Hv; first by intros [=].
    destruct (to_vals es') as [vs|] eqn:Hvs; last by intros [=].
    intros [= <- <- <-]. split; last done. simpl.
    by erewrite of_to_vals.
Qed.

Lemma decompose_step_sound e k e' :
  decompose_step e = Some (k, e') →
  filli k e' = e.
Proof.
  revert k e'.
  induction e; intros k e'; simpl;
    repeat match goal with
    | |- context [match to_val ?x with _ => _ end] =>
        let H := fresh "Hv" in destruct (to_val x) as [|] eqn:H
    | H : to_val ?x = Some _ |- _ => apply of_to_val in H; subst x
    end;
    try (intros [=]; subst; reflexivity);
    try done.
  - (* Block *)
    destruct (split_block es) as [[[pre hole] suf]|] eqn:Hsb; last by intros [=].
    intros [= <- <-]. simpl.
    destruct (split_block_sound _ _ _ _ Hsb) as [-> _]. done.
Qed.

Lemma decompose_fuel_sound n e :
  fill (decompose_fuel n e).1 (decompose_fuel n e).2 = e.
Proof.
  revert e. induction n as [|n IH]; intros e; simpl; first done.
  destruct (decompose_step e) as [[k e']|] eqn:Hds; last done.
  destruct (decompose_fuel n e') as [K r] eqn:Heq.
  simpl. rewrite fill_snoc.
  specialize (IH e'). rewrite Heq in IH. simpl in IH. rewrite IH.
  by apply decompose_step_sound.
Qed.

Lemma decompose_sound e :
  fill (decompose e).1 (decompose e).2 = e.
Proof. apply decompose_fuel_sound. Qed.

(* ---------- [fill]-redex precision ---------- *)

(** A [filli k _] is never a value. *)
Lemma to_val_filli k e :
  to_val (filli k e) = None.
Proof. by destruct k. Qed.

(** [fill K e] is a value only when [K = []] and [e] is. *)
Lemma to_val_fill K e :
  to_val e = None →
  to_val (fill K e) = None.
Proof.
  revert e. induction K as [|k K IH]; intros e Hv; first exact Hv.
  change (fill (k :: K) e) with (fill K (filli k e)).
  apply IH. apply to_val_filli.
Qed.

(** [split_block] of a list of pure values returns [None]. *)
Lemma split_block_of_vals vs :
  split_block (of_vals vs) = None.
Proof.
  induction vs as [|v vs IH]; first done.
  simpl. rewrite IH. reflexivity.
Qed.

(** [split_block] applied to [es ++ hole :: of_vals vs] locates [hole]. *)
Lemma split_block_app es hole vs :
  to_val hole = None →
  split_block (es ++ hole :: of_vals vs) = Some (es, hole, vs).
Proof.
  intros Hv. induction es as [|e es IH]; simpl.
  - rewrite split_block_of_vals. rewrite Hv. rewrite to_of_vals. reflexivity.
  - rewrite IH. reflexivity.
Qed.

(** Peeling: [decompose_step (filli k X) = Some (k, X)] when [X] is a
    non-value. *)
Lemma decompose_step_filli k X :
  to_val X = None →
  decompose_step (filli k X) = Some (k, X).
Proof.
  destruct k; intros HX; simpl; try (rewrite HX; reflexivity).
  - (* CtxBlock *) rewrite (split_block_app _ _ _ HX). reflexivity.
Qed.

(** Fuelled variant of the main lemma, parameterised over the fuel budget. *)
Lemma decompose_fuel_fill K n e :
  to_val e = None →
  decompose_step e = None →
  n ≥ length K →
  decompose_fuel n (fill K e) = (K, e).
Proof.
  intros Hv Hd. revert n.
  induction K as [|k K IH] using rev_ind; intros n Hn.
  - destruct n as [|n']; first done.
    simpl. rewrite Hd. reflexivity.
  - rewrite fill_snoc.
    rewrite length_app in Hn. simpl in Hn.
    destruct n as [|n']; first lia.
    simpl. rewrite decompose_step_filli; last by apply to_val_fill.
    rewrite IH; [reflexivity|lia].
Qed.

(** Each [filli k _] adds at least one to [expr_size]. *)
Lemma expr_size_filli k e :
  expr_size (filli k e) ≥ S (expr_size e).
Proof.
  induction k; simpl; try lia.
  - (* CtxBlock *)
    rewrite map_app. simpl. rewrite list_sum_app. simpl. lia.
Qed.

(** [expr_size] of [fill K e] dominates [length K]. *)
Lemma expr_size_fill K e :
  expr_size (fill K e) ≥ length K + expr_size e.
Proof.
  revert e. induction K as [|k K IH]; intros e; first (simpl; lia).
  change (fill (k :: K) e) with (fill K (filli k e)).
  pose proof (IH (filli k e)) as IH'.
  pose proof (expr_size_filli k e). simpl. lia.
Qed.

(** [decompose] of [fill K e] returns exactly [(K, e)] when [e] is a
    non-value redex (no further surface decomposition). *)
Lemma decompose_fill_redex K e :
  to_val e = None →
  decompose_step e = None →
  decompose (fill K e) = (K, e).
Proof.
  intros Hv Hd. unfold decompose.
  apply decompose_fuel_fill; [done|done|].
  pose proof (expr_size_fill K e). lia.
Qed.

(** [decompose_step] only ever exposes a non-value sub-expression. *)
Lemma decompose_step_not_val e k e' :
  decompose_step e = Some (k, e') → to_val e' = None.
Proof.
  revert k e'. induction e; simpl; intros k e' Heq;
    repeat (case_match; simplify_eq); try done; try by eauto.
  match goal with
  | H : split_block _ = Some _ |- _ => apply split_block_sound in H; tauto
  end.
Qed.

(** The redex reached by [decompose_fuel] (with enough fuel) is a head redex. *)
Lemma decompose_fuel_redex_no_step n e :
  n ≥ expr_size e → decompose_step (decompose_fuel n e).2 = None.
Proof.
  revert e. induction n as [|n IH]; intros e Hn.
  - exfalso. destruct e; simpl in Hn; lia.
  - simpl. destruct (decompose_step e) as [[k e']|] eqn:Hds; last exact Hds.
    destruct (decompose_fuel n e') as [K r] eqn:Hr. simpl.
    pose proof (decompose_step_sound _ _ _ Hds) as Hfill.
    pose proof (expr_size_filli k e') as Hsz.
    assert (Hn' : n ≥ expr_size e') by (rewrite <- Hfill in Hn; lia).
    specialize (IH e' Hn'). rewrite Hr in IH. exact IH.
Qed.

(** The redex reached by [decompose_fuel] from a non-value is itself a non-value. *)
Lemma decompose_fuel_redex_not_val n e :
  to_val e = None → n ≥ expr_size e → to_val (decompose_fuel n e).2 = None.
Proof.
  revert e. induction n as [|n IH]; intros e Hv Hn.
  - exfalso. destruct e; simpl in Hn; lia.
  - simpl. destruct (decompose_step e) as [[k e']|] eqn:Hds; last exact Hv.
    destruct (decompose_fuel n e') as [K r] eqn:Hr. simpl.
    pose proof (decompose_step_sound _ _ _ Hds) as Hfill.
    pose proof (decompose_step_not_val _ _ _ Hds) as Hv'.
    pose proof (expr_size_filli k e') as Hsz.
    assert (Hn' : n ≥ expr_size e') by (rewrite <- Hfill in Hn; lia).
    specialize (IH e' Hv' Hn'). rewrite Hr in IH. exact IH.
Qed.

Lemma decompose_redex_no_step e :
  decompose_step (decompose e).2 = None.
Proof. unfold decompose. apply decompose_fuel_redex_no_step. lia. Qed.

Lemma decompose_redex_not_val e :
  to_val e = None → to_val (decompose e).2 = None.
Proof. intros. unfold decompose. apply decompose_fuel_redex_not_val; [done|lia]. Qed.
