From iris.proofmode Require Import base proofmode.

From mizzle.lang Require Export semantics.

From mizzle.logic Require Import interp goal adequacy wf_access
  most_general_client completeness_lin.
From mizzle.pure_logic Require Import linear.

(** * Adequacy for non-linearizability of the most-general client.

    A hand-driven most-general-client run that deposits the [Trace T] witness
    yields a real reduction whose observation trace decodes to [T] *and* is
    non-linearizable. The non-linearizability half reuses the [is_non_lin]
    witness from [completeness_lin] — a finished [Trace T] (with [T]
    pure-non-linearizable) is itself an [is_non_lin] witness. *)

Section adequacy_lin.
Context `{seqlogGS Σ}.
Context `{M : model}.

(** A finished [Trace T] over a non-linearizable [T] is an [is_non_lin]
    witness: against any [interp], the real observation trace is pinned to [T]. This
    is the bridge from the driver's [Trace] witness to [completeness_lin]'s
    [is_non_lin]. *)
Lemma Trace_is_non_lin T :
  trace_non_linearizable T →
  Trace T -∗ is_non_lin.
Proof.
  iIntros (Hnl) "(%obs & Hpm & %Hdec)".
  iIntros (es σ ts) "Hi".
  iDestruct (interp_trace with "Hi Hpm") as %->.
  iPureIntro. rewrite Hdec. exact Hnl.
Qed.

(** Read-off pinning *both* the concrete trace and its non-linearizability off
    a single [interp]. The concrete-trace read ([Trace_read]) and the
    non-linearizability witness ([is_non_lin] via [deduce_non_lin]) share the
    same [interp_trace] fact, so [interp] is consumed exactly once. *)
Lemma Trace_read_non_lin T es σ ts :
  trace_non_linearizable T →
  interp es σ ts -∗ Trace T -∗
  ⌜decode_trace ts = T ∧ trace_non_linearizable (decode_trace ts)⌝.
Proof.
  iIntros (Hnl) "Hi (%obs & Hpm & %Hdec)".
  iDestruct (interp_trace with "Hi Hpm") as %->.
  iPureIntro. rewrite Hdec. split; [done | exact Hnl].
Qed.

End adequacy_lin.

(** Adequacy wrapper: drive [prog] (depositing [Trace T] via [Trace_fulfill]);
    given [T] is pure-non-linearizable, the resulting real reduction's
    observation trace decodes to [T] and is non-linearizable. [[card]] *)
Lemma mgc_non_lin_adequacy `{M : model} (prog : expr) (T : list (positive * trace)) :
  trace_non_linearizable T →
  (∀ Σ (hG : seqlogGS Σ),
     running 0 prog -∗ Trace [] -∗ remaining (Trace T) -∗ goal ⊤) →
  ∃ c κ,
    wf_access.traced_steps ([prog], initial_state ValUnit) κ c ∧
    decode_trace κ = T ∧
    trace_non_linearizable (decode_trace κ).
Proof.
  intros Hnl Hdrive.
  edestruct (goal_adequacy_trace_tr (λ Σ hG, Trace T) prog ValUnit
               (λ ts _, decode_trace ts = T ∧ trace_non_linearizable (decode_trace ts)))
    as (c & κ & Hsteps & Hpost).
  2:{ exists c, κ. split; [exact Hsteps | exact Hpost]. }
  intros Σ hG. iIntros "(Hrem & Hrun & Hloc0 & Htm)".

  iDestruct (Trace_intro with "Htm") as "Htr".
  iSplitL "Hrem Hrun Htr".
  2:{ iIntros (es σ ts) "(Hi & HQ)".
      iApply (Trace_read_non_lin T _ _ _ Hnl with "Hi HQ"). }
  iApply (Hdrive Σ hG with "Hrun Htr Hrem").
Qed.
