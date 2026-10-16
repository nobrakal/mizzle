From iris.proofmode Require Import base proofmode.

From mizzle.lang Require Export semantics.
From mizzle.lang Require Import instances.

From mizzle.logic Require Import interp goal adequacy translate wf_access completeness
  most_general_client.
From mizzle.pure_logic Require Import linear.

(** * Completeness for (non-)linearizability.

    [mirror] exposes the shadow observation list, which decodes to the trace
    the program emitted. This is the hook for turning "the logic reproduces
    every real execution" into a statement about linearizability of the
    emitted trace. *)

(** * Step 1: [decode_trace] commutes with the [ψ]-renaming, unconditionally.

    [tr_val ψ] is a structural homomorphism that only permutes locations, and
    [decode_event] inspects nothing but tags/booleans/ints (all preserved) plus
    the payload value [x]. Hence decoding the renamed trace equals renaming the
    decoded trace, with no assumption on payloads. *)

(** Renaming action on a decoded trace event: apply [tr_val ψ] to the payload. *)
Definition tr_event (ψ : gmap location location) (t : trace) : trace :=
  match t with
  | Call v     => Call (tr_val ψ v)
  | Lin  v v'  => Lin  (tr_val ψ v) (tr_val ψ v')
  | Ret  v'    => Ret  (tr_val ψ v')
  end.

Lemma decode_event_tr_val ψ o :
  decode_event (tr_val ψ o) = (λ pt, (pt.1, tr_event ψ pt.2)) <$> decode_event o.
Proof.
  rewrite /decode_event.
  destruct o as [| |gen tag vs]; cbn; try done.
  destruct gen; cbn; try done. destruct tag; cbn; try done.
  destruct vs as [|x0 [|x1 [|x2 vs]]]; cbn; try done.
  all: destruct x0 as [l| |]; cbn; try done.
  all: destruct l as [?|?|?|]; cbn; try done.
  all: destruct x1 as [| |gen1 tag1 vs1]; cbn; try done.
  all: destruct gen1; cbn; try done. all: destruct tag1; cbn; try done.
  all: destruct vs1 as [|y0 [|y1 [|y2 vs1]]]; cbn; try done.
  all: destruct y0 as [l0| |]; cbn; try done.
  all: destruct l0 as [b0|?|?|]; cbn; try done.
  all: destruct b0; cbn; try done.
Qed.

Lemma decode_trace_tr_val ψ xs :
  decode_trace (tr_val ψ <$> xs) = (λ pt, (pt.1, tr_event ψ pt.2)) <$> decode_trace xs.
Proof.
  rewrite /decode_trace. induction xs as [|o xs IH]; [done|].
  rewrite fmap_cons /= decode_event_tr_val.
  unfold omap in IH; destruct (decode_event o) as [pt|]; simpl; rewrite IH //.
Qed.

(** * "No location in the trace" route.

    If the emitted trace carries no locations, then [tr_val ψ] fixes every
    payload, so the shadow trace held by [mirror] is *equal* to the real trace
    (not merely a renaming of it) — and non-linearizability transfers directly,
    with no model assumption. *)

(** [tr_val ψ] fixes a location-free value. *)
Lemma tr_val_loc_free ψ v : locs_val v = ∅ → tr_val ψ v = v.
Proof.
  intros Hv. transitivity (tr_val ∅ v).
  - symmetry. apply (tr_val_agree ψ ∅ v). intros k Hk. rewrite Hv in Hk. set_solver.
  - apply tr_val_empty.
Qed.

(** Predicate: a list of observations carries no locations. *)
Definition obs_loc_free (xs : list observation) : Prop :=
  Forall (λ o, locs_val o = ∅) xs.

(** Under [obs_loc_free], the [ψ]-renaming is the identity on the trace. *)
Lemma tr_obs_trace_loc_free ψ xs :
  obs_loc_free xs → tr_val ψ <$> xs = xs.
Proof.
  induction 1 as [|o xs H1 _ IH]; [done|].
  by rewrite fmap_cons (tr_val_loc_free _ _ H1) IH.
Qed.

Section non_lin.
Context `{seqlogGS Σ}.
Context `{M : model}.

(** Logic-side non-linearizability witness — same [interp]-witness shape as
    [is_racy]/[is_stuck]: against any [interp], the real reduction's
    observation trace decodes to a non-linearizable trace. *)
Definition is_non_lin : iProp Σ :=
  ∀ es σ ts, interp es σ ts -∗
    ⌜trace_non_linearizable (decode_trace (ts))⌝.

(** Read-off (analogue of [deduce_racy]): [is_non_lin] held against [interp]
    pins the real reduction's observation trace as non-linearizable. *)
Lemma deduce_non_lin es σ ts :
  interp es σ ts -∗ is_non_lin -∗
  ⌜trace_non_linearizable (decode_trace (ts))⌝.
Proof. iIntros "Hi Hnl". by iApply ("Hnl" with "Hi"). Qed.

(** Completeness core (analogue of [is_racy_complete]): from [mirror es σ κ],
    a non-linearizable *location-free* emitted trace yields [is_non_lin].
    The shadow trace held by [mirror] is [tr_val ψ <$> κ], which
    under [obs_loc_free] equals [κ] verbatim. *)
Lemma is_non_lin_complete es σ κ :
  trace_non_linearizable (decode_trace (κ)) →
  obs_loc_free (κ) →
  mirror es σ κ -∗ is_non_lin.
Proof.
  intros Hnl Hlf. iIntros "Hm". rewrite mirror_unfold.
  iDestruct "Hm" as (φ ψ Hok) "(_ & _ & _ & _ & _ & Hpm)".
  rewrite (tr_obs_trace_loc_free ψ _ Hlf).
  iIntros (es' σ' ts') "Hi".
  iDestruct (interp_trace with "Hi Hpm") as %Heq.
  iPureIntro. rewrite -Heq. exact Hnl.
Qed.

End non_lin.

(** Completeness for non-linearizability.

    Any *real* (traced) execution whose emitted trace is non-linearizable is
    reproduced by the logic: from the reachable configuration the logic
    derives [goal ⊤] while fulfilling the non-linearizability witness [is_non_lin]. Stated in the [completeness_race]
    style (the [goal]-producing entailment).

    The trace is now a real index of [mirror] (via the generalized
    [completeness] over [traced_steps]), which pins the shadow trace to
    [tr_val ψ <$> κ]. Under the "no location in the trace"
    hypothesis [obs_loc_free (κ)] this equals the real trace
    [κ] verbatim, so [is_non_lin] follows directly with no model
    assumption (see [is_non_lin_complete]). *)
Theorem completeness_non_linearizable `{M : model} e v0 es σ κ :
  traced_steps ([e], initial_state v0) κ (es, σ) →
  trace_non_linearizable (decode_trace (κ)) →
  obs_loc_free (κ) →
  locs_expr e = ∅ → locs_val v0 = ∅ →
  (∀ `{hG : !seqlogGS Σ},
    remaining is_non_lin ∗ running 0 e ∗ local 0 v0 ∗ trace_model [] -∗
    goal ⊤).
Proof.
  intros Hsteps Hnl Hlf Hloe Hlov0.
  iIntros (??) "(Hrem & Hrun & Hlocal & Hpm)".
  iApply (completeness e v0 es σ κ Hsteps Hloe Hlov0).
  iFrame "Hrun Hlocal Hpm".
  iApply (update_remaining with "[] Hrem").
  iApply (is_non_lin_complete es σ κ Hnl Hlf).
Qed.
