# Guide: proving a concurrent program racy

Proving that a program has a **data race**
with mizzle's goal-CPS driver.

> **⚠️ Evaluation is RIGHT-TO-LEFT** (`src/lang/semantics.v`; inherited from
> Zoo). The next redex is the *rightmost* unevaluated sub-expression: in
> `f e1 e2`, `e2` reduces before `e1`, both after `f` becomes a value. A tactic
> that "can't find" a manifestly present redex is usually looking off the eval
> spine — reduce the redexes to its right first.

---

## 1. Two tiers of steps — what you may look up

- **Primitive steps** — `fun:`/`rec:`, calling a lambda, `let:`, `;;`,
  `match:`, `if:`, unop/binop/`==`, an applied constructor or tuple, `ref`,
  `!`/`<-` (atomic or not), a CAS (the `atomic_loc٠cas` wrapper or the raw
  `CAS`), `Fork`, `for:`, `while:`, **and `array٠make`/`array٠get`/`array٠set`** — are
  driven *only* by the `g_*` tactics of §4. Each takes hypothesis names and
  nothing else. The lemmas behind them (`focused_*_at`,
  `focused_atomic_loc_*`, `focused_array_*`) are internal: never open
  `goal_tactics.v`, `goal_proof.v`, `atomic_loc.v` or `array.v` to see what
  a tactic does.
- **Calls with no tactic** — other lemmas are applied by hand (§5).
  For a statement not on that card (§7), ask the warm MCP session
  (`About x.`, `Search f.`) rather than reading a file.

---

## 2. MCP workflow

- **Warm once, first.** Before any other tool call, `rocq_start` in preamble
  mode with the `Require` block the task gives you (it is the import block of
  §3 instantiated for the case), `workspace` = absolute path to `theories/`.
  It stays cached; every later `rocq_check` is fast. Never call `rocq_start`
  again — unless the session died (`Pet process died`, `State … expired`).
- **Order of work:** read the *entire* `main` body → confirm which two
  accesses race (same address, ≥1 write, ≥1 non-atomic) → drive both
  threads → close → wire the theorem.
- **Plan before driving.** Decide which two accesses race and which
  resources each thread needs; the large units are a loop, a fork, the
  close. Draft each unit in full and submit it as one `rocq_check`.
- **Develop interactively**, then paste the final script into the file:
  `rocq_check` to step and inspect, `rocq_step_multi` to try several candidate
  tactics without committing.
- **Whole-file check** with `rocq_compile_file`, `file`
  relative to the workspace and `workspace` given.
- **Pass `timeout: 300`** to the final `rocq_check`, the one ending in
  `Qed`: the 30 s default is too short for `Qed` on large proofs.

---

## 3. The canonical proof — a complete file

Every solution is one file: the import block below (order matters: the
case's `__code` last), one `Section` with a **driving lemma** that parks two
racing threads, and a one-line **pure top theorem**. `drb001_antidep` in
full — it exercises nearly the whole API:

```coq

From mizzle.dataracebench.support Require Import drb_prelude.
From mizzle.stdlib Require Import array.
From mizzle.dataracebench.cases Require Import drb001_antidep__code.

Section proof.
Context `{seqlogGS Σ}.

(** [a[i] := i] for [i] in [0,1000), then [parallel_for 999 (fun i => a[i] :=
    a[i+1] + 1)]. Thread 0 reads [a[1]], thread 1 writes [a[1]]: same address,
    one write, both non-atomic. Park thread 0 at the raw [GetField] of [a[1]]
    and thread 1 at the raw [SetField] of [a[1]]. *)
Lemma drb001_racy_goal p ks :
  remaining is_racy' -∗
  focused p ks (App (Val drb001_antidep٠main) (Val ValUnit)) -∗
  goal ⊤.
Proof.
iIntros "Hrem Hrun".
rewrite /drb001_antidep٠main.
g_call "Hrun". g_let "Hrun".
g_array_make "Hrun" a "Hhdr_a" "Hcells_a".    (* fresh [a], □ header, 1000 cells *)
g_let "Hrun".
iDestruct (zcells_of_replicate with "Hcells_a") as "Hza".
g_focus (For _ _ _) "Hrun".                   (* sequenced loop: focus it first *)
(* march the init loop generically — see §6 *)
iApply (focused_loop_inv ⊤ p (fun _ => zcells a 0 (Z.to_nat 1000))%I 0 1000 _ _
          with "[] [Hza] Hrun"); first lia.
{ iModIntro. iIntros (i ks' Hi) "Hz Hf Hcont".   (* □ body: [Hhdr_a] stays in scope *)
  g_rec "Hf". g_call "Hf".
  iDestruct (zcells_acc a 0 (Z.to_nat 1000) i with "Hz") as "[Hc Hz']"; first lia.
  iDestruct "Hc" as (z) "Hc".
  g_array_set "Hf" "Hhdr_a" "Hc".
  iApply ("Hcont" with "[Hz' Hc] Hf"). iApply "Hz'". by iFrame. }
{ iFrame. }
iIntros "Hza Hrun". iEval (simpl) in "Hrun".
g_let "Hrun". g_rec "Hrun".
g_args "Hrun".
iEval (rewrite (val_int_of_nat 999 ltac:(lia))) in "Hrun".
iApply (drb٠parallel_for_spec with "Hrun").
iIntros (qs kss Hlen Hlen') "Hthreads _".
destruct qs as [|q0 [|q1 qs]]; try (simpl in Hlen; lia).
destruct kss as [|ks0 [|ks1 kss]]; try (simpl in Hlen'; lia).
iDestruct "Hthreads" as "(Hq0 & Hq1 & _)".
(* thread q0 (i = 0): park at the raw GetField of a[1] *)
g_call "Hq0".
(* carve the two racing cells out of the generic block, once *)
iDestruct (zcells_split a 0 (Z.to_nat 1000) 2 with "Hza") as "[Hz01 Hz2]"; first lia.
iDestruct (zcells_acc a 0 2 1 with "Hz01") as "[Hc1 _]"; first lia.
iDestruct (zcells_acc a (0 + Z.of_nat 2) _ 2 with "Hz2") as "[Hc2 _]"; first lia.
iDestruct "Hc1" as (z1) "Hc1". iDestruct "Hc2" as (z2) "Hc2".
g_args "Hq0".
g_array_get_to_get_field "Hq0" "Hhdr_a".
(* thread q1 (i = 1): read a[2], then park at the raw SetField of a[1] *)
g_call "Hq1". g_args "Hq1".
g_array_get "Hq1" "Hhdr_a" "Hc2".
g_args "Hq1".
g_array_set_to_set_field "Hq1" "Hhdr_a".
iApply (goal_race_close q0 q1 with "Hrem Hq0 Hq1"); [solve_access..| solve_races].
Qed.

End proof.

Theorem drb001_antidep_racy v0 :
  exists c, rtc silent_step ([(drb001_antidep٠main ())%E], initial_state v0) c /\ racy c.
Proof. apply goal_race_adequacy. intros. apply drb001_racy_goal. Qed.
```

---

## 4. API map

**Notation conventions.**

- A closure is an *expression* while written `fun: x => e` /
  `rec: f x => e` and a *value* once written `vfun:` / `vrec:`; `g_rec` turns
  the former into the latter.
- `!e`, `e1 <- e2`, `e.{fld}`, `e1 <-{fld} e2` are `NotAtomic`; the atomic
  forms carry a superscript (`!ᵃᵗ`, `<-ᵃᵗ`).
- `ref v` is a one-field mutable block.
- A record is one block with one slot per field, and `(ref a, ref b)` is two
  blocks plus a tuple.
- A CAS in generated code is the wrapper call
  `atomic_loc٠cas t ⟨fld⟩ old new`, not the primitive `CAS`; the
  `g_cas_*` tactics fire on both.
- A spec lemma wanting `body : val` unifies only with the `vfun:` form.
- A source `=` compiles to a *call* `structeq e1 e2`, not to the primitive
  `Equal`: once both arguments are integer literals, apply
  `focused_structeq_int` (§7, exported by the prelude), which leaves
  `#(bool_decide (z1 = z2))`; then `destruct (bool_decide (z1 = z2)) eqn:Hb`
  and, in each branch, `iEval (simpl) in "H"` followed by `g_if_true` /
  `g_if_false`.

**Stepping.** Each tactic takes a *named* running hypothesis, finds its redex
by `reshape_expr` (no manual focus), and rebinds under the same name.

| Redex as printed | Constructor | Tactic |
|-|-|-|
| `fun: x => e`, `rec: f x => e` (→ `vfun:`/`vrec:`) | `Rec f x e` | `g_rec` |
| `v1 v2` (value applied to value) | `App (Val _) (Val _)` | `g_call` (multi-arg: `g_call2/3/4`) |
| `let: x := v in e`, `v ;; e` | `Let`, `Seq` | `g_let`, `g_seq` |
| `if: v then _ else _` | `If (Val _) _ _` | `g_if`, `g_if_true`, `g_if_false` |
| `match: v with …` | `Match (Val _) _ _ _` | `g_match` |
| `- v`, `v1 + v2`, `v1 == v2` | `Unop`, `Binop`, `Equal` | `g_unop`, `g_binop`, `g_equal` |
| `ref v` | `Block Mutable …` | `g_alloc "H" "Hl"` (fresh `l`, `Hl : l ↦∗ [v]`) |
| `!v`, `!ᵃᵗ v`, `v.{fld}` | `GetField _ (Val _) (Val _)` | `g_get_field "H" "Hl"` |
| `v <- w`, `v <-ᵃᵗ w`, `v <-{fld} w` | `SetField _ (Val _) (Val _) (Val _)` | `g_set_field "H" "Hl"` (`Hl` updated in place) |
| `array٠get #a #i`, `array٠set #a #i v` | | step: `g_array_get "H" "Hhdr" "Hc"`, `g_array_set "H" "Hhdr" "Hc"`; park at the raw `GetField`/`SetField`: `g_array_get_to_get_field "H" "Hhdr"`, `g_array_set_to_set_field "H" "Hhdr"` |
| `‘Some( v )`, `v :: vs`, `(v1, v2)` (all fields values) | `Block _ _ [Val …]` | `g_block` (fixpoint, inside-out; `g_tuple` for tuples only) |
| `for: i := #lo to #n begin e end` | `For (Val _) (Val _) _` | `g_for` |
| `while: e0 begin e1 end` | `While _ _` | `g_while` (unfolds one iteration to `if: e0 then (e1 ;; while: e0 begin e1 end) else ()`) |
| `atomic_loc٠cas t ⟨fld⟩ old new`, `CAS d old new` | wrapper call / `CAS` | `g_cas_succ "H" "Hl"`, `g_cas_fail "H" "Hl"` |
| `Fork e` | `Fork _` | `g_fork "H" "Hc" "Hl"` (child `Hc : running q (fill [] e)`) |
| `structeq #z1 #z2` (source `=`) | `App (App (Val structeq) _) _` | `focused_structeq_int` by hand, see above |
| `array٠make #n v` | | `g_array_make "H" a "Hhdr" "Hcells"` (fresh `a`, □ header, `replicate n v` cells) |

Plus `g_focus efoc "Hp"` (fold a context onto `ks`, no step), and `g_args "Hp"`
(= `repeat g_binop` then `g_znorm`, which computes closed integer
literals). The `g_array_*` tactics find the first fully-applied
`array٠get`/`set` on the spine and discharge both bounds by `lia`.

**Race and adequacy.** The shared address evar in `access` doubles as the
same-location check.

| | |
|---|---|
| `remaining is_racy' -∗ focused p ks (main ()) -∗ goal ⊤` | driving-lemma shape |
| `goal_race_close q1 q2` | packages `fulfill` + `update_remaining` + `is_racy_intro` |
| `solve_access` / `solve_races` | find each access redex on the spine; discharge the write/atomicity side |
| `goal_race_adequacy` | pure top theorem, one line |

---

## 5. Spec lemmas applied by hand

**Finding the lemma.** A call `f` with no tactic is stepped by what
`Search f.` returns (`rocq_query`). The card in §7 is the cached result of
those searches for the current library — a lemma absent from it is found
the same way. Every spec lemma is stated on a bare redex,
`focused p ks (redex) -∗ …`, and `iApply` unifies *syntactically*. Before
applying one:

1. **Reduce.** Every argument the statement matches on must be a literal
   value: `g_args "H"` for arithmetic, `g_block` for a constructor, `g_rec`
   for a closure; a named constant is unfolded first with
   `iEval (rewrite /name) in "H"`.
2. **Focus.** `g_focus (shape) "H"` so the redex is the whole focused
   expression; `shape` is the lemma's argument with holes, e.g. `(For _ _ _)`.
3. **Pass `_`** for everything the term fixes (`lo`, `n`, `body`, sizes);
   supply only your choices (the invariant, `mid`).
4. **Goal order.** Coq premises first (`; first lia` for a bound), then one
   goal per `[…]` in the `with` pattern in order, then the continuation.
5. **Afterwards**, `iSimpl in "H"` before the next pure step: a hand
   application leaves `fill K (Val v)` unsimplified.

---

## 6. Loop marching

Do not write per-shape loop inductions. Two lemmas (§7) march a thread
through `For #lo #n body` under an arbitrary invariant `I : Z → iProp`:

- `focused_loop_inv E p I lo n body ks` — run to completion; the
  continuation gets `I n` and the thread at `()`.
- `focused_loop_prefix E p I lo mid n body ks` — run `[lo, mid)` only; the
  thread is parked at `For #mid #n body`, from where the remaining iterations
  can be stepped one at a time with `g_for`.

In `with "[] [Hres] H"` (§3), the three goals are the body, the resources
for `I lo`, and the thread. Two things about the body are not optional:

- **It is a `□` goal.** `iModIntro` keeps the persistent context (the □
  headers) and clears the spatial one, so only spatial resources the body
  needs travel inside `I`; then `iIntros (i ks' Hi) "HI Hf Hcont"`.
- **It starts `g_rec "Hf". g_call "Hf".`** — generated loop bodies are
  `fun:` expressions.

---

## 7. API card

<!-- API CARD: generated by gen_api_card.py, do not edit -->

`src/stdlib/array.v`

```coq
Definition zcells (l : location) (base : Z) (count : nat) : iProp Σ :=
  ([∗ list] k ∈ seq 0 count, ∃ z:Z, (l +ₗ (base + Z.of_nat k)%Z) ↦ ValInt z)%I.
```

`src/stdlib/array.v`

```coq
Lemma zcells_of_replicate l (n:nat) (z:Z) :
  ([∗ list] k ↦ w ∈ replicate n (ValInt z), (l +ₗ Z.of_nat k) ↦ w) -∗
  zcells l 0 n.
```

`src/stdlib/array.v`

```coq
Lemma zcells_split l (base:Z) (count n1 : nat) :
  (n1 <= count)%nat →
  zcells l base count -∗
  zcells l base n1 ∗ zcells l (base + Z.of_nat n1) (count - n1).
```

`src/stdlib/array.v`

```coq
Lemma zcells_acc l (base:Z) (count:nat) (i:Z) :
  (base <= i < base + Z.of_nat count)%Z →
  zcells l base count -∗
  (∃ z:Z, (l +ₗ i) ↦ ValInt z) ∗
  ((∃ z:Z, (l +ₗ i) ↦ ValInt z) -∗ zcells l base count).
```

`src/logic/goal_tactics.v`

```coq
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
```

`src/logic/goal_tactics.v`

```coq
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
```

`src/dataracebench/support/drb_axiom.v`

```coq
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
```

`src/dataracebench/support/drb_axiom.v`

```coq
Axiom drb٠parallel_for_spec :
  ∀ `{seqlogGS Σ}, parallel_for_spec drb٠parallel_for.
```

`src/dataracebench/support/drb_axiom.v`

```coq
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
```

`src/dataracebench/support/drb_axiom.v`

```coq
Axiom drb٠parallel_for_chunked_spec :
  ∀ `{seqlogGS Σ}, parallel_for_chunked_spec drb٠parallel_for_chunked.
```

`src/dataracebench/support/drb_axiom.v`

```coq
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
```

`src/dataracebench/support/drb_axiom.v`

```coq
Axiom array٠make_matrix_spec :
  ∀ `{seqlogGS Σ}, make_matrix_spec array٠make_matrix.
```

`src/dataracebench/support/drb_axiom.v`

```coq
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
```

`src/stdlib/structeq.v`

```coq
Lemma focused_structeq_int E p ks (z1 z2 : Z) :
  focused p ks (App (App (Val structeq) (Val (ValInt z1))) (Val (ValInt z2))) -∗
  (focused p ks (Val (ValBool (bool_decide (z1 = z2)))) -∗ goal E) -∗
  goal E.
```

`src/logic/race.v`

```coq
Lemma goal_race_close p1 p2 e1 e2 l k1 k2 :
  access e1 l k1 ->
  access e2 l k2 ->
  races k1 k2 ->
  remaining is_racy' -∗ running p1 e1 -∗ running p2 e2 -∗ goal ⊤.
```

`src/logic/interp.v`

```coq
Lemma mz_pointsto_ne l1 dq1 v1 l2 dq2 v2 :
  l1 ↦{dq1} v1 -∗ l2 ↦{dq2} v2 -∗ ⌜l1 ≠ l2⌝.
```

<!-- END API CARD -->
