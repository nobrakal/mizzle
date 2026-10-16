From mizzle.lang Require Import
  prelude.
From mizzle.lang Require Import
  instances.
From mizzle.stdlib Require Import
  domain.

From iris.proofmode Require Import base proofmode.

From mizzle.logic Require Import interp goal goal_proof goal_tactics.
From mizzle.stdlib Require Import domain array.
From mizzle.dataracebench.support Require Import drb_axiom.
From mizzle.lang Require Import
  options.

(** Plain MizzleLang realizations of the [drb_axiom] primitives. *)

(* [drb٠parallel_for #n body] runs [body #i] for every [i ∈ [0, n)] in
   parallel. We realize it by divide and conquer on the interval
   [lo, hi): split at the midpoint, spawn a domain for the left half,
  run the right half in the current domain, then join.

  Unrealisitic because spawns a lot of domains *)
Definition drb٠parallel_for : val :=
  vfun: "n" "body" =>
    letrec: "go" "lo" "hi" :=
      if: "hi" - "lo" ≤ #0 then (
        ()
      ) else if: "hi" - "lo" == #1 then (
        "body" "lo"
      ) else (
        let: "mid" := "lo" + ("hi" - "lo") `quot` #2 in
        let: "t" := domain٠spawn (fun: <> => "go" "lo" "mid") in
        "go" "mid" "hi" ;;
        domain٠join "t"
      )
    in
    "go" #0 "n".

(** [drb٠parallel_for_chunked #c #n body] runs [body #i] for every
    [i ∈ [0, n)], scheduling iterations in chunks of size [c]: one domain
    per chunk [k], running [body #i] for [i ∈ [k*c, min (k*c + c) n)]
    sequentially. Chunks are spawned one after the other and joined on
    the way back up the recursion. *)
Definition drb٠parallel_for_chunked : val :=
  vfun: "c" "n" "body" =>
    let: "chunk" := fun: "lo" =>
      let: "hi" := if: "lo" + "c" ≤ "n" then "lo" + "c" else "n" in
      for: "i" := "lo" to "hi" begin
        "body" "i"
      end
    in
    letrec: "go" "lo" :=
      if: "n" ≤ "lo" then (
        ()
      ) else (
        let: "t" := domain٠spawn (fun: <> => "chunk" "lo") in
        "go" ("lo" + "c") ;;
        domain٠join "t"
      )
    in
    "go" #0.

(** [array٠make_matrix #sx #sy v] allocates an outer array of [sx] cells,
    then fills each cell with a fresh row [array٠make #sy v], mirroring
    OCaml's [Array.make_matrix]. *)
Definition array٠make_matrix : val :=
  vfun: "sx" "sy" "v" =>
    let: "t" := array٠make "sx" () in
    for: "i" := 0 to "sx" begin
      array٠unsafe_set "t" "i" (array٠make "sy" "v")
    end ;;
    "t".

(** * Realization proofs *)

Section proof.
Context `{seqlogGS Σ}.

Notation focused p ks e := (running p (fill ks e)).

(** The recursive worker of [drb٠parallel_for], with [body] substituted:
    the closure value [go] obtained after the [letrec:] step. *)
Definition pf_go (body : val) : val :=
  (vrec: "go" "lo" "hi" =>
     if: "hi" - "lo" ≤ #0 then (
       ()
     ) else if: "hi" - "lo" == #1 then (
       body "lo"
     ) else (
       let: "mid" := "lo" + ("hi" - "lo") `quot` #2 in
       let: "t" := domain٠spawn (fun: <> => "go" "lo" "mid") in
       "go" "mid" "hi" ;;
       domain٠join "t"
     ))%V.

(** Specification of [pf_go body #lo #(lo+m)], by strong induction on the
    interval length [m]: the continuation receives [m] processes, each
    focused on [body #(lo+k)] under some context; once all have been
    driven to [()], resuming runs the pending joins and hands back the
    calling process [r] with the whole call reduced to [()]. The process
    [r] itself runs one of the iterations (the rightmost leaf of the
    divide-and-conquer tree); the others are spawned domains. *)
Lemma go_spec E (body : val) (m : nat) :
  ∀ (r : nat) (kr : list ectxi) (lo : nat),
  ⊢ focused r kr (App (App (Val (pf_go body)) (Val (ValInt lo)))
                      (Val (ValInt (lo + m)%nat))) -∗
    (∀ (qs : list nat) (kss : list (list ectxi)),
       ⌜length qs = m⌝ -∗ ⌜length kss = m⌝ -∗
       ([∗ list] k ↦ q;ksq ∈ qs;kss,
          focused q ksq (App (Val body) (Val (ValInt (lo + k)%nat)))) -∗
       (([∗ list] q;ksq ∈ qs;kss, focused q ksq (Val ValUnit)) -∗
        (focused r kr (Val ValUnit) -∗ goal E) -∗ goal E) -∗
       goal E) -∗
    goal E.
Proof.
  induction (lt_wf m) as [m _ IH].
  intros r kr lo.
  iIntros "Hr Hcont".
  rewrite {1}/pf_go. g_call2 "Hr".
  (* [hi - lo] *)
  g_binop "Hr".
  assert (Hsub : (Z.of_nat (lo + m) - Z.of_nat lo)%Z = Z.of_nat m) by lia.
  rewrite Hsub.
  (* [… ≤ 0] *)
  g_binop "Hr".
  destruct m as [|m1].
  { (* m = 0 : empty interval *)
    case_bool_decide; last lia.
    g_if_true "Hr".
    iApply ("Hcont" $! [] [] with "[//] [//] [//]").
    iIntros "_ HK". iApply ("HK" with "Hr"). }
  case_bool_decide; first lia.
  g_if_false "Hr".
  (* [hi - lo == 1] *)
  g_binop "Hr". rewrite Hsub.
  destruct m1 as [|m2].
  { (* m = 1 : leaf, [r] itself runs [body #lo] *)
    g_equal "Hr". g_if_true "Hr".
    iApply ("Hcont" $! [r] [kr] with "[//] [//] [Hr]").
    { simpl. rewrite Nat.add_0_r. by iFrame. }
    iIntros "(Hr & _) HK". iApply ("HK" with "Hr"). }
  g_equal "Hr". case_bool_decide; first lia.
  g_if_false "Hr".
  (* compute [mid = lo + m/2] *)
  g_binop "Hr". rewrite Hsub.
  g_binop "Hr".
  assert (Hq : (Z.of_nat (S (S m2)) ÷ 2)%Z = Z.of_nat (S (S m2) `div` 2)).
  { rewrite Z.quot_div_nonneg; try lia. }
  rewrite Hq.
  g_binop "Hr". rewrite -Nat2Z.inj_add.
  g_let "Hr".
  replace ((Nat.divmod m2 1 1 1).1) with (S (S m2) `div` 2) by reflexivity.
  set (mm := S (S m2)) in *.
  set (m1 := mm `div` 2).
  assert (Hm1pos : 0 < m1) by (apply Nat.div_str_pos; lia).
  assert (Hm1lt : m1 < mm) by (apply Nat.div_lt; lia).
  set (m2' := mm - m1).
  assert (Hm2pos : 0 < m2') by (unfold m2'; lia).
  assert (Hm2lt : m2' < mm) by (unfold m2'; lia).
  (* spawn a domain [c] for the left half [lo, lo+m1) *)
  g_rec "Hr".
  g_focus (App (Val domain٠spawn) (Val _)) "Hr".
  iApply (goal_domain_spawn with "Hr").
  iIntros (t c ksc) "Hh Hc Hr". iEval (simpl) in "Hr".
  g_let "Hr".
  g_call "Hc".
  iPoseProof (IH m1 Hm1lt c ksc lo) as "IHc".
  iApply ("IHc" with "[Hc]").
  { rewrite /pf_go. iExact "Hc". }
  iIntros (qs1 kss1 Hlen1 Hlen1') "Hb1 HW1".
  (* run the right half [lo+m1, lo+mm) in [r], under the pending join *)
  assert (Heq : (lo + mm)%nat = ((lo + m1) + m2')%nat) by (unfold m2'; lia).
  rewrite Heq.
  g_focus (App (App (Val _) (Val _)) (Val _)) "Hr".
  iPoseProof (IH m2' Hm2lt r _ (lo + m1)%nat) as "IHr".
  iApply ("IHr" with "[Hr]").
  { rewrite /pf_go. iExact "Hr". }
  iIntros (qs2 kss2 Hlen2 Hlen2') "Hb2 HW2".
  (* hand all [mm] iterations to the continuation *)
  iApply ("Hcont" $! (qs1 ++ qs2) (kss1 ++ kss2) with "[%] [%] [Hb1 Hb2]").
  { rewrite length_app. lia. }
  { rewrite length_app. lia. }
  { iApply (big_sepL2_app with "Hb1 [Hb2]").
    rewrite Hlen1.
    iApply (big_sepL2_mono with "Hb2").
    intros; simpl. rewrite Nat.add_assoc //. }
  (* resume: collect both halves, then run the pending join *)
  iIntros "Hfin HK".
  iDestruct (big_sepL2_app_inv with "Hfin") as "[Hf1 Hf2]".
  { left. lia. }
  iApply ("HW1" with "Hf1"). iIntros "Hc".
  iApply ("HW2" with "Hf2"). iIntros "Hr".
  iEval (simpl) in "Hr".
  g_let "Hr".
  iApply (goal_domain_join with "Hr Hh Hc").
  iIntros "Hr". iApply ("HK" with "Hr").
Qed.

(** The divide-and-conquer realization implements the axiom's spec. *)
Lemma parallel_for_realized :
  parallel_for_spec drb٠parallel_for.
Proof.
  intros E p ks n body.
  iIntros "Hp Hcont".
  rewrite /drb٠parallel_for.
  g_call2 "Hp". g_rec "Hp". g_let "Hp".
  iApply (go_spec E body n p ks 0 with "Hp Hcont").
Qed.

(** * The chunked version *)

(** The chunk worker of [drb٠parallel_for_chunked], with [c], [n] and
    [body] substituted: runs [body #i] for [i ∈ [lo, min (lo+c) n)]
    sequentially. *)
Definition pf_chunk (body : val) (c n : nat) : val :=
  (vfun: "lo" =>
     let: "hi" := if: "lo" + #c ≤ #n then "lo" + #c else #n in
     for: "i" := "lo" to "hi" begin
       body "i"
     end)%V.

(** The recursive chunk scheduler: one domain per chunk. *)
Definition pf_chunk_go (body : val) (c n : nat) : val :=
  (vrec: "go" "lo" =>
     if: #n ≤ "lo" then (
       ()
     ) else (
       let: "t" := domain٠spawn (fun: <> => pf_chunk body c n "lo") in
       "go" ("lo" + #c) ;;
       domain٠join "t"
     ))%V.

(** The [for:] loop of a chunk realizes the [one_chunk_spec] protocol:
    each iteration exposes [body #i] under the pending-loop context, and
    each resume (which carries the goal) steps the loop scaffolding to
    the next iteration. [d] is fuel for the induction ([m - i ≤ d]). *)
Lemma chunk_loop_spec E q ksq (body : val) (m : nat) :
  ∀ (d i : nat), m - i ≤ d →
  ⊢ focused q ksq (For (Val (ValInt i)) (Val (ValInt m))
                       (Rec BAnon (BNamed "i") (App (Val body) (Var "i")))) -∗
    (one_chunk_spec E q body i m (focused q ksq (Val ValUnit)) -∗ goal E) -∗
    goal E.
Proof.
  induction d as [|d IHd]; intros i Hd; iIntros "Hq Hcont".
  { (* fuel 0: m ≤ i *)
    g_for "Hq". iApply "Hcont".
    rewrite one_chunk_spec_equation_1.
    case_decide; last lia.
    iExact "Hq". }
  destruct (decide (m ≤ i)) as [Hle|Hlt].
  { (* loop done *)
    g_for "Hq". iApply "Hcont".
    rewrite one_chunk_spec_equation_1.
    case_decide; last lia.
    iExact "Hq". }
  (* one more iteration: expose [body #i] *)
  g_for "Hq".
  g_rec "Hq". g_call "Hq".
  g_focus (App (Val body) (Val _)) "Hq".
  iApply "Hcont".
  rewrite one_chunk_spec_equation_1.
  case_decide; first lia.
  iExists _. iFrame "Hq".
  (* resume: step the loop to the next iteration *)
  iIntros (v) "Hq HG".
  iEval (rewrite -focused_bind; simpl) in "Hq".
  g_let "Hq".
  assert (Hsucc : (Z.of_nat i + 1)%Z = Z.of_nat (S i)) by lia.
  rewrite Hsucc.
  iApply (IHd (S i) with "Hq"); first lia.
  iExact "HG".
Qed.

(** Specification of [pf_chunk_go body c n #(j*c)], by induction on the
    fuel [d] bounding the remaining iterations: one [one_chunk_spec] per
    remaining chunk; resuming runs the pending joins. *)
Lemma chunked_go_spec E (body : val) (c n : nat) :
  0 < c →
  ∀ (d j : nat) (r : nat) (kr : list ectxi),
  n - j * c ≤ d →
  j * c < n + c →
  ⊢ focused r kr (App (Val (pf_chunk_go body c n)) (Val (ValInt (j * c)%nat))) -∗
    (∀ (qs : list nat) (kss : list (list ectxi)),
       ⌜n ≤ (j + length qs) * c < n + c⌝ -∗
       ⌜length kss = length qs⌝ -∗
       ([∗ list] k ↦ q;ksq ∈ qs;kss,
          one_chunk_spec E q body ((j + k) * c) (min ((j + k) * c + c) n)
            (focused q ksq (Val ValUnit))) -∗
       (([∗ list] q;ksq ∈ qs;kss, focused q ksq (Val ValUnit)) -∗
        (focused r kr (Val ValUnit) -∗ goal E) -∗ goal E) -∗
       goal E) -∗
    goal E.
Proof.
  intros Hc.
  induction d as [|d IHd]; intros j r kr Hd Hinv; iIntros "Hr Hcont".
  { (* fuel 0: n ≤ j*c, no chunk left *)
    rewrite {1}/pf_chunk_go. g_call "Hr".
    g_binop "Hr".
    case_bool_decide; last lia.
    g_if_true "Hr".
    iApply ("Hcont" $! [] [] with "[%] [//] [//]").
    { simpl. lia. }
    iIntros "_ HK". iApply ("HK" with "Hr"). }
  rewrite {1}/pf_chunk_go. g_call "Hr".
  g_binop "Hr".
  destruct (decide (n ≤ j * c)) as [Hdone|Hmore].
  { (* no chunk left *)
    case_bool_decide; last lia.
    g_if_true "Hr".
    iApply ("Hcont" $! [] [] with "[%] [//] [//]").
    { simpl. lia. }
    iIntros "_ HK". iApply ("HK" with "Hr"). }
  case_bool_decide; first lia.
  g_if_false "Hr".
  (* spawn a domain [cq] for chunk [j] *)
  g_rec "Hr".
  g_focus (App (Val domain٠spawn) (Val _)) "Hr".
  iApply (goal_domain_spawn with "Hr").
  iIntros (t cq ksc) "Hh Hc Hr". iEval (simpl) in "Hr".
  g_let "Hr".
  (* the child runs its chunk: compute [hi = min (j*c + c) n] … *)
  g_call "Hc".
  iEval (rewrite /pf_chunk) in "Hc". g_call "Hc".
  g_binop "Hc".
  rewrite -Nat2Z.inj_add.
  g_binop "Hc".
  (* … and its [for:] loop realizes [one_chunk_spec] (both [min] cases) *)
  iAssert (one_chunk_spec E cq body (j * c) ((j * c + c) `min` n)
             (focused cq ksc (Val ValUnit)) -∗ goal E)%I
    with "[-Hc]" as "Hrest"; last first.
  { destruct (decide (j * c + c ≤ n)) as [Hfull|Hpart].
    - (* full chunk: hi = j*c + c *)
      case_bool_decide; last lia.
      g_if_true "Hc".
      g_binop "Hc".
      rewrite -Nat2Z.inj_add.
      g_let "Hc".
      replace ((j * c + c) `min` n) with (j * c + c) by lia.
      iApply (chunk_loop_spec E cq ksc body (j * c + c) (j * c + c) (j * c)
                with "[Hc]"); first lia.
      { iExact "Hc". }
      iExact "Hrest".
    - (* last, partial chunk: hi = n *)
      case_bool_decide; first lia.
      g_if_false "Hc".
      g_let "Hc".
      replace ((j * c + c) `min` n) with n by lia.
      iApply (chunk_loop_spec E cq ksc body n n (j * c) with "[Hc]"); first lia.
      { iExact "Hc". }
      iExact "Hrest". }
  iIntros "Hone".
  (* recurse on the remaining chunks, under the pending join *)
  g_binop "Hr".
  assert (Hstep : (Z.of_nat (j * c) + Z.of_nat c)%Z = Z.of_nat (S j * c)).
  { rewrite Nat.mul_succ_l. lia. }
  rewrite Hstep.
  g_focus (App (Val _) (Val _)) "Hr".
  iPoseProof (IHd (S j) r _) as "IHr".
  { rewrite Nat.mul_succ_l. lia. }
  { rewrite Nat.mul_succ_l. lia. }
  iApply ("IHr" with "[Hr]").
  { rewrite /pf_chunk_go /pf_chunk. iExact "Hr". }
  iIntros (qs' kss' Hlen' Hlen'') "Hb HW".
  (* hand all remaining chunks to the continuation *)
  iApply ("Hcont" $! (cq :: qs') (ksc :: kss') with "[%] [%] [Hone Hb]").
  { simpl. replace (j + S (length qs')) with (S j + length qs') by lia. lia. }
  { simpl. lia. }
  { simpl.
    rewrite Nat.add_0_r.
    iFrame "Hone".
    iApply (big_sepL2_mono with "Hb").
    intros; simpl.
    replace (j + S k) with (S j + k) by lia.
    auto. }
  (* resume: collect the tail, then run the pending join *)
  iIntros "Hfin HK". simpl.
  iDestruct "Hfin" as "[Hfc Hfin]".
  iApply ("HW" with "Hfin"). iIntros "Hr".
  g_let "Hr".
  iApply (goal_domain_join with "Hr Hh Hfc").
  iIntros "Hr". iApply ("HK" with "Hr").
Qed.

(** The one-domain-per-chunk realization implements the axiom's spec. *)
Lemma parallel_for_chunked_realized :
  parallel_for_chunked_spec drb٠parallel_for_chunked.
Proof.
  intros E p ks c n body Hc.
  iIntros "Hp Hcont".
  rewrite /drb٠parallel_for_chunked.
  g_call3 "Hp".
  g_rec "Hp". g_let "Hp".
  g_rec "Hp". g_let "Hp".
  iApply (chunked_go_spec E body c n Hc n 0 p ks with "[Hp] [Hcont]");
    [lia|lia| |].
  { rewrite /pf_chunk_go /pf_chunk. iExact "Hp". }
  iIntros (qs kss Hlen Hlen') "Hb HW".
  iApply ("Hcont" $! qs kss with "[%] [//] [Hb] [HW]");
    [simpl in Hlen; lia| |].
  { iExact "Hb". }
  iExact "HW".
Qed.

(** * [make_matrix] *)

(** The row-filling loop of [array٠make_matrix]: from counter [i], the [d]
    remaining cells (still holding [()]) each receive a fresh row. *)
Lemma make_matrix_loop E p ks (l : location) (sx : nat) (sy : Z) (v : val) :
  (0 ≤ sy)%Z →
  ∀ (d i : nat), i + d = sx →
  ⊢ l ↦ₕ□ Header 0 sx -∗
    ([∗ list] k ↦ w ∈ replicate d ValUnit, (l +ₗ Z.of_nat (i + k)) ↦ w) -∗
    focused p ks (For (Val (ValInt i)) (Val (ValInt sx))
      (Rec BAnon (BNamed "i")
         (App (App (App (Val array٠unsafe_set) (Val (ValLoc l))) (Var "i"))
              (App (App (Val array٠make) (Val (ValInt sy))) (Val v))))) -∗
    (∀ rows : list location,
       ⌜length rows = d⌝ -∗
       ([∗ list] k ↦ r ∈ rows, (l +ₗ Z.of_nat (i + k)) ↦ ValLoc r) -∗
       ([∗ list] r ∈ rows,
          r ↦ₕ□ Header 0 (Z.to_nat sy) ∗
          [∗ list] j ↦ w ∈ replicate (Z.to_nat sy) v, (r +ₗ Z.of_nat j) ↦ w) -∗
       focused p ks (Val ValUnit) -∗ goal E) -∗
    goal E.
Proof.
  intros Hsy.
  induction d as [|d IHd]; intros i Hd; iIntros "#Hhdr Hc Hp Hcont".
  { (* loop done *)
    g_for "Hp".
    iApply ("Hcont" $! [] with "[//] [//] [//] Hp"). }
  (* one more iteration: allocate row [r], store it at [l[i]] *)
  g_for "Hp".
  g_rec "Hp". g_call "Hp".
  g_array_make "Hp" r "Hrh" "Hrc".
  iDestruct "Hc" as "[Hhead Htail]". rewrite Nat.add_0_r.
  g_focus (App (App (App (Val array٠unsafe_set) (Val _)) (Val _)) (Val _)) "Hp".
  iApply (focused_array_unsafe_set with "Hhdr Hhead Hp"); [lia|lia|].
  iIntros "_ Hhead Hp". iEval (simpl) in "Hp".
  g_seq "Hp".
  replace (Z.of_nat i + 1)%Z with (Z.of_nat (S i)) by lia.
  iApply (IHd (S i) with "Hhdr [Htail] Hp"); first lia.
  { iApply (big_sepL_mono with "Htail"). iIntros (k x ?) "Hk".
    replace (i + S k) with (S i + k) by lia. done. }
  iIntros (rows Hrows) "Hcells Hrows Hp".
  iApply ("Hcont" $! (r :: rows) with "[%] [Hhead Hcells] [Hrh Hrc Hrows] Hp").
  { simpl. lia. }
  { simpl. rewrite Nat.add_0_r. iFrame "Hhead".
    iApply (big_sepL_mono with "Hcells"). iIntros (k x ?) "Hk".
    replace (i + S k) with (S i + k) by lia. done. }
  { simpl. iFrame "#∗". }
Qed.

(** The row-by-row realization implements the axiom's spec. *)
Lemma make_matrix_realized :
  make_matrix_spec array٠make_matrix.
Proof.
  intros E p ks sx sy v Hsx Hsy.
  iIntros "Hp Hcont".
  rewrite /array٠make_matrix.
  g_call3 "Hp".
  g_array_make "Hp" l "Hhdr" "Hc".
  g_let "Hp".
  iEval (rewrite (val_int_of_nat sx Hsx)) in "Hp".
  g_focus (For _ _ _) "Hp".
  iApply (make_matrix_loop E p _ l (Z.to_nat sx) sy v Hsy (Z.to_nat sx) 0
            with "Hhdr [Hc] Hp"); first lia.
  { iApply (big_sepL_mono with "Hc"). iIntros (k x ?) "Hk". done. }
  iIntros (rows Hrows) "Hcells Hrows Hp". iEval (simpl) in "Hp".
  g_seq "Hp".
  iApply ("Hcont" with "[//] Hhdr Hcells Hrows Hp").
Qed.

End proof.
