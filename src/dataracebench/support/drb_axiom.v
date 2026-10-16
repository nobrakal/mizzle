From Equations Require Import Equations.

From iris.proofmode Require Import base proofmode.

From mizzle.lang Require Export semantics.

From mizzle.logic Require Import interp goal goal_proof goal_tactics.

From mizzle.stdlib Require Import domain.

Parameter drb٠parallel_for : val.

(** Intermediate definition of the [parallel_for] specification,
    parameterized by the implementation [pf].

    [pf #n body] runs [body #i] for every [i ∈ [0, n)] in parallel: the
    continuation receives [n] processes [qs], each running [body #i]
    under a universally quantified evaluation context [kss !! i] (an
    implementation is free to run the iterations under whatever wrapper
    it needs — e.g. a fork/join scaffolding). Once every iteration has
    been driven to [()], the resume wand hands the parent process back,
    with [pf #n body] reduced to [()]. [[card]] *)
Definition parallel_for_spec `{seqlogGS Σ} (pf : val) : Prop :=
  ∀ E p ks (n : nat) (body : val),
    ⊢ running p (fill ks (pf #n body)) -∗
      (∀ (qs : list nat) (kss : list (list ectxi)),
         ⌜length qs = n⌝ -∗ ⌜length kss = n⌝ -∗
         ([∗ list] i ↦ q;ksq ∈ qs;kss, running q (fill ksq (body #i))) -∗
         (([∗ list] q;ksq ∈ qs;kss, running q (fill ksq ValUnit)) -∗
          (running p (fill ks ValUnit) -∗ goal E) -∗ goal E) -∗
         goal E) -∗
      goal E.

(** The [parallel_for] of the generated programs meets the specification. [[card]] *)
Axiom drb٠parallel_for_spec :
  ∀ `{seqlogGS Σ}, parallel_for_spec drb٠parallel_for.

(** The iteration count of a generated program is an integer literal; the
    axiom's [n : nat] enters as [#(Z.to_nat n)]. *)
Lemma val_int_of_nat (n : Z) : (0 <= n)%Z → (#n : val) = #(Z.to_nat n).
Proof. intros. simpl. by rewrite Z2Nat.id. Qed.

Parameter drb٠parallel_for_chunked : val.

(** Sequential protocol of one chunk, in goal-CPS style. *)
Equations one_chunk_spec `{seqlogGS Σ} (E : coPset) (q:nat) (f:expr) (i m:nat) (K : iProp Σ) : iProp Σ by wf (m-i) lt :=
one_chunk_spec E q f i m K :=
  (if decide (m <= i) then K else
   ∃ ks', running q (fill ks' (f #i)) ∗
          (∀ v, running q (fill ks' (Val v)) -∗
                (one_chunk_spec E q f (S i) m K -∗ goal E) -∗ goal E))%I.
Next Obligation. intros. lia. Qed.

(** Intermediate definition of the [parallel_for_chunked] specification,
    parameterized by the implementation [pf]. [[card]] *)
Definition parallel_for_chunked_spec `{seqlogGS Σ} (pf : val) : Prop :=
  ∀ E p ks (c n : nat) (body : val),
    0 < c →
    ⊢ running p (fill ks (pf #c #n body)) -∗
      (∀ (qs : list nat) (kss : list (list ectxi)),
         ⌜n ≤ length qs * c < n + c⌝ -∗
         ⌜length kss = length qs⌝ -∗
         ([∗ list] k ↦ q;ksq ∈ qs;kss,
            one_chunk_spec E q body (k * c) (min (k * c + c) n)
              (running q (fill ksq ValUnit))) -∗
         (([∗ list] q;ksq ∈ qs;kss, running q (fill ksq ValUnit)) -∗
          (running p (fill ks ValUnit) -∗ goal E) -∗ goal E) -∗
         goal E) -∗
      goal E.

(** The [parallel_for_chunked] of the generated programs meets the specification. [[card]] *)
Axiom drb٠parallel_for_chunked_spec :
  ∀ `{seqlogGS Σ}, parallel_for_chunked_spec drb٠parallel_for_chunked.

Parameter array٠make_matrix : val.

(** Intermediate definition of the [make_matrix] specification,
    parameterized by the implementation [mm].

    [mm #sx #sy v] allocates the outer array [l] of [sx]
    row-locations (a tag-[0] block, like every MizzleLang array), each row [r] being
    a freshly-allocated inner array of [sy] cells all initialized to [v]. The
    rows are pairwise distinct allocations (mirroring OCaml's [make_matrix]:
    one [unsafe_alloc] per row), so we hand out their full cell ownership. [[card]] *)
Definition make_matrix_spec `{seqlogGS Σ} (mm : val) : Prop :=
  ∀ E p ks (sx sy : Z) (v : val),
    (0 ≤ sx)%Z → (0 ≤ sy)%Z →
    ⊢ running p (fill ks (mm #sx #sy v)) -∗
      (∀ (l : location) (rows : list location),
         ⌜length rows = Z.to_nat sx⌝ -∗
         l ↦ₕ□ Header 0 (Z.to_nat sx) -∗
         ([∗ list] i ↦ r ∈ rows, (l +ₗ Z.of_nat i) ↦ ValLoc r) -∗
         ([∗ list] r ∈ rows,
            r ↦ₕ□ Header 0 (Z.to_nat sy) ∗
            [∗ list] j ↦ w ∈ replicate (Z.to_nat sy) v, (r +ₗ Z.of_nat j) ↦ w) -∗
         running p (fill ks (Val (ValLoc l))) -∗ goal E) -∗
      goal E.

(** The [make_matrix] of the generated programs meets the specification. [[card]] *)
Axiom array٠make_matrix_spec :
  ∀ `{seqlogGS Σ}, make_matrix_spec array٠make_matrix.

(** [drb٠par f g] runs [f ()] in a freshly spawned domain and [g ()] in the
    current one, then joins the domain, returning the result of [f ()]. It
    is defined (not axiomatized) as the translation of [Drb.par]. *)
Definition drb٠par : val :=
  vfun: "f" "g" =>
    let: "t" := domain٠spawn "f" in
    "g" () ;;
    domain٠join "t".

Section par.
Context `{seqlogGS Σ}.

(** [drb٠par f g] forks: the continuation receives the spawned process [q]
    focused on [f ()] and the caller [p] focused on [g ()], each under an
    abstract context. Once [f ()] has reduced to [v] and [g ()] to some
    [w], the resume wand performs the join and hands back [p] with the
    whole call reduced to [v]. [[card]] *)
Lemma drb_par_spec (E : coPset) p ks (f g : val) :
  running p (fill ks (drb٠par f g)) -∗
  (∀ q ksq ksp,
     running q (fill ksq (App (Val f) (Val ValUnit))) -∗
     running p (fill ksp (App (Val g) (Val ValUnit))) -∗
     (∀ v w,
        running q (fill ksq (Val v)) -∗
        running p (fill ksp (Val w)) -∗
        (running p (fill ks (Val v)) -∗ goal E) -∗ goal E) -∗
     goal E) -∗
  goal E.
Proof.
  iIntros "Hp Hcont". rewrite /drb٠par. g_call2 "Hp".
  (* spawn [q] on [f ()] *)
  g_focus (App (Val domain٠spawn) (Val _)) "Hp".
  iApply (goal_domain_spawn with "Hp").
  iIntros (t q ksq) "Hh Hq Hp". iEval (simpl) in "Hp".
  g_let "Hp".
  (* [p] runs [g ()] under the pending join *)
  iApply ("Hcont" $! q ksq (CtxLet BAnon _ :: ks) with "Hq [Hp]");
    first iExact "Hp".
  iIntros (v w) "Hq Hp HK". iEval (simpl) in "Hp".
  g_let "Hp".
  iApply (goal_domain_join with "Hp Hh Hq").
  iIntros "Hp". iApply ("HK" with "Hp").
Qed.

End par.
