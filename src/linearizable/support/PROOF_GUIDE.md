# Guide: proving a concurrent data structure non-linearizable

Proving that a data structure is **not
linearizable** with mizzle's **most-general-client** (`_mgc`) framework and
its goal-CPS driver.

> **⚠️ Evaluation is RIGHT-TO-LEFT** (`src/lang/semantics.v`; inherited from
> Zoo). The next redex is the *rightmost* unevaluated sub-expression: in
> `f e1 e2`, `e2` reduces before `e1`, both after `f` becomes a value. A tactic
> that "can't find" a manifestly present redex is usually looking off the eval
> spine — reduce the redexes to its right first. In particular, the `ref`s of
> a constructor or tuple are **allocated last field first**: in `create`, read
> `obj` off the goal — `#l`, `(#l1, #l0)%V`, `#arr` — never guess the
> location↔field mapping.

---

## 1. Two tiers of steps — what you may look up

- **Primitive steps** — `fun:`/`rec:`, calling a lambda, `let:`, `;;`,
  `match:`, `if:`, unop/binop/`==`, an applied constructor or tuple, `ref`,
  `!`/`<-` (atomic or not), a CAS (the `atomic_loc٠cas` wrapper or the raw
  `CAS`), `Fork`, `for:`, `while:`, **and `array٠get`/`array٠set`** — are driven
  *only* by the `g_*` tactics of §4. Each takes hypothesis names and nothing
  else. The lemmas behind them (`focused_*_at`, `focused_atomic_loc_*`,
  `focused_array_*`) are internal: never open `goal_tactics.v`,
  `goal_proof.v`, `atomic_loc.v` or `array.v` to see what a tactic does.
- **Calls with no tactic** — other lemmas are applied by hand (§5).
  For a statement not on that card (§7), ask the warm MCP session
  (`About x.`, `Search f.`) rather than reading a file.

The sequential model is given; the preamble imports it.

---

## 2. MCP workflow

- **Warm once, first.** Before any other tool call, `rocq_start` in preamble
  mode with the `Require` block the task gives you (it is the import block of
  §3 instantiated for the case), `workspace` = absolute path to `theories/`.
  It stays cached; every later `rocq_check` is fast. Never call `rocq_start`
  again — unless the session died (`Pet process died`, `State … expired`).
- **Order of work:** read `create` and every method `op` dispatches to →
  pick the bug → design the witness trace (§6) → Theorem 1 → `gen` and its
  `goal_gen_*` drivers → drive the schedule in Theorem 2 → `Trace_fulfill`.
- **Plan before driving.** A proof is a few large predictable units:
  `create` and the fork skeleton, then one `call ; driver ; ret` block per
  trace event, in trace order, each driver a straight line of `g_*` steps
  mirroring the method's body. Draft each unit in full and submit it as one
  `rocq_check`.
- **Develop interactively**, then paste the final script into the file:
  `rocq_check` to step and inspect, `rocq_step_multi` to try several candidate
  tactics without committing.
- **Whole-file check** with `rocq_compile_file`, `file`
  relative to the workspace and `workspace` given.
- **Pass `timeout: 300`** to the final `rocq_check`, the one ending in
  `Qed`: the 30 s default is too short for `Qed` on large proofs.

---

## 3. The canonical proof — a complete file

Every solution is one file: the import block (order matters: the prelude,
then the model, then the case's `__code` and `__types`), the `init`/`op`
glue, the **trace** `Definition`, the generator **`gen`**, one `Section
helpers` holding one `goal_gen_*` driver per request value, the pure
**Theorem 1** (`per_tag_complete` + `trace_non_linearizable`), and the
fixed-name **Theorem 2** `mgc_produces_non_linearizable`, which drives the
real client along the witness schedule and ends with `Trace_fulfill`.
`key_buggy_stack` in full — it exercises nearly the whole API:

```coq
(** key_buggy_stack: Treiber stack whose push compares against a fresh
    re-read instead of its snapshot, under the most general client.

    key_buggy_stack٠push reads the contents into "xs", builds "ys" = v :: xs,
    then CASes with expected value [!ᵃᵗ "t"] -- a second, fresh read -- rather
    than "xs". The CAS therefore always succeeds against whatever is current,
    but stores the list built from the stale "xs": a concurrent push that
    landed in between is silently overwritten, even though it already
    returned.

    Witness: two concurrent Push calls (tags 1 and 2) both read the initial
    (empty) contents. Push(2) (tag 2) completes uncontended, storing [2].
    Push(1) (tag 1) resumes: its fresh re-read sees [2], its CAS succeeds
    against [2], and it stores its stale-based [1], discarding [2] for good.
    Both pushes have completed before two Pop calls (tags 3 and 4) run to
    completion: since Push(2) really completed, every linearization must
    place it somewhere, so the two later Pops must together see two
    elements -- but the real execution yields one (1), then an empty
    response. Not linearizable. *)

From mizzle.linearizable.support Require Import mgc_prelude.

From mizzle.pure_logic Require Import stack_model.
From mizzle.linearizable.cases Require Import
  key_buggy_stack__code key_buggy_stack__types.

Definition init : val := key_buggy_stack٠create.
Definition op : val := key_buggy_stack٠op.

Notation valid_op := stack_valid_request.

Definition lost_push_trace : list (positive * trace) := [
  (1%positive, Call (‘SPush( #1 ))%V) ;
  (2%positive, Call (‘SPush( #2 ))%V) ;
  (2%positive, Ret (§None)%V) ;
  (1%positive, Ret (§None)%V) ;
  (3%positive, Call (§SPop)%V) ;
  (3%positive, Ret (‘Some( #1 ))%V) ;
  (4%positive, Call (§SPop)%V) ;
  (4%positive, Ret (§None)%V)
].

Definition gen : val :=
  vfun: <> =>
    if: nondet_bool () then ‘Push( #1 )
    else if: nondet_bool () then ‘Push( #2 ) else §Pop.

Section helpers.
Context `{seqlogGS Σ}.

Lemma goal_gen_push1 E pp ks :
  running pp (fill ks (gen (Val ValUnit))) -∗
  (running pp (fill ks (Val (‘Push( #1 ))%V)) -∗ goal E) -∗ goal E.
Proof.
  iIntros "Hp Hcont". rewrite /gen. g_call "Hp".
  iApply (goal_rand _ pp (CtxIf _ _ :: ks) true with "Hp"). iIntros "Hp".
  iSimpl in "Hp". g_if_true "Hp". g_block "Hp".
Qed.

Lemma goal_gen_push2 E pp ks :
  running pp (fill ks (gen (Val ValUnit))) -∗
  (running pp (fill ks (Val (‘Push( #2 ))%V)) -∗ goal E) -∗ goal E.
Proof.
  iIntros "Hp Hcont". rewrite /gen. g_call "Hp".
  iApply (goal_rand _ pp (CtxIf _ _ :: ks) false with "Hp"). iIntros "Hp".
  iSimpl in "Hp". g_if_false "Hp".
  iApply (goal_rand _ pp (CtxIf _ _ :: ks) true with "Hp"). iIntros "Hp".
  iSimpl in "Hp". g_if_true "Hp". g_block "Hp".
Qed.

Lemma goal_gen_pop E pp ks :
  running pp (fill ks (gen (Val ValUnit))) -∗
  (running pp (fill ks (Val (§Pop)%V)) -∗ goal E) -∗ goal E.
Proof.
  iIntros "Hp Hcont". rewrite /gen. g_call "Hp".
  iApply (goal_rand _ pp (CtxIf _ _ :: ks) false with "Hp"). iIntros "Hp".
  iSimpl in "Hp". g_if_false "Hp".
  iApply (goal_rand _ pp (CtxIf _ _ :: ks) false with "Hp"). iIntros "Hp".
  iSimpl in "Hp". g_if_false "Hp".
Qed.

End helpers.

Lemma lost_push_trace_per_tag_complete : per_tag_complete lost_push_trace.
Proof.
  intros τ.
  destruct (decide (τ = 1%positive)); subst.
  { exists (‘SPush( #1 ))%V, (§None)%V. right. vm_compute. reflexivity. }
  destruct (decide (τ = 2%positive)); subst.
  { exists (‘SPush( #2 ))%V, (§None)%V. right. vm_compute. reflexivity. }
  destruct (decide (τ = 3%positive)); subst.
  { exists (§SPop)%V, (‘Some( #1 ))%V. right. vm_compute. reflexivity. }
  destruct (decide (τ = 4%positive)); subst.
  { exists (§SPop)%V, (§None)%V. right. vm_compute. reflexivity. }
  exists ()%V, ()%V. left.
  unfold lost_push_trace.
  repeat (rewrite filter_cons_False; [|cbn; intros ?; subst; done]).
  apply filter_nil.
Qed.

Theorem lost_push_trace_not_linearizable : trace_non_linearizable lost_push_trace.
Proof.
  apply is_non_linearizable_check_sound.
  - solve_call_valid.
  - exact lost_push_trace_per_tag_complete.
  - by vm_compute.
Qed.

Theorem mgc_produces_non_linearizable :
  ∃ c κ,
    wf_access.traced_steps ([(most_general_client init op gen)%E], initial_state ValUnit) κ c ∧
    decode_trace κ = lost_push_trace ∧
    trace_non_linearizable (decode_trace κ).
Proof.
  apply (mgc_non_lin_adequacy (most_general_client init op gen) lost_push_trace
           lost_push_trace_not_linearizable).
  intros Σ hG. iIntros "Hrun Htr Hrem".
  rewrite /most_general_client. g_call3 "Hrun".
  rewrite /init /key_buggy_stack٠create. g_call "Hrun".
  g_alloc "Hrun" "Ht". g_let "Hrun".
  g_rec "Hrun". g_let "Hrun".
  g_rec "Hrun". g_let "Hrun".
  g_call "Hrun".
  iApply (goal_rand _ 0 [CtxIf _ _] false with "Hrun"). iIntros "Hrun". iSimpl in "Hrun". g_if_false "Hrun".
  g_fork "Hrun" "Hc1" "Hl1". g_seq "Hrun". g_binop "Hrun". g_call "Hrun".
  iApply (goal_rand _ 0 [CtxIf _ _] false with "Hrun"). iIntros "Hrun". iSimpl in "Hrun". g_if_false "Hrun".
  g_fork "Hrun" "Hc2" "Hl2". g_seq "Hrun". g_binop "Hrun". g_call "Hrun".
  iApply (goal_rand _ 0 [CtxIf _ _] false with "Hrun"). iIntros "Hrun". iSimpl in "Hrun". g_if_false "Hrun".
  g_fork "Hrun" "Hc3" "Hl3". g_seq "Hrun". g_binop "Hrun". g_call "Hrun".
  iApply (goal_rand _ 0 [CtxIf _ _] false with "Hrun"). iIntros "Hrun". iSimpl in "Hrun". g_if_false "Hrun".
  g_fork "Hrun" "Hc4" "Hl4". g_seq "Hrun". g_binop "Hrun". g_call "Hrun".
  iApply (goal_rand _ 0 [CtxIf _ _] true with "Hrun"). iIntros "Hrun". iSimpl in "Hrun". g_if_true "Hrun".

  (* tag=1: Push(1) -- snapshots the empty contents into "xs", builds [1],
     and parks right before the CAS's fresh re-read. *)
  iApply (goal_onecall_call ⊤ op #l gen p' [] 1 (‘Push( #1 ))%V _ goal_gen_push1 with "Hc1 Htr"). iIntros "Hc1 Htr".
  iEval (rewrite /op /key_buggy_stack٠op) in "Hc1". g_call2 "Hc1". g_match "Hc1".
  rewrite /key_buggy_stack٠push. g_call2 "Hc1".
  g_get_field "Hc1" "Ht". g_let "Hc1". g_block "Hc1". g_let "Hc1".

  (* tag=2: Push(2) -- runs to completion uncontended, storing [2]. *)
  iApply (goal_onecall_call ⊤ op #l gen p'0 [] (1+1) (‘Push( #2 ))%V _ goal_gen_push2 with "Hc2 Htr"). iIntros "Hc2 Htr".
  iEval (rewrite /op /key_buggy_stack٠op) in "Hc2". g_call2 "Hc2". g_match "Hc2".
  rewrite /key_buggy_stack٠push. g_call2 "Hc2".
  g_get_field "Hc2" "Ht". g_let "Hc2". g_block "Hc2". g_let "Hc2".
  g_get_field "Hc2" "Ht". g_cas_succ "Hc2" "Ht". g_unop "Hc2". g_if_false "Hc2". g_seq "Hc2".
  iApply (goal_onecall_ret ⊤ p'0 [] (1+1) §None%V _ with "Hc2 Htr"). iIntros "Hc2 Htr".

  (* tag=1: resume -- the fresh re-read sees [2], so the CAS succeeds against
     it and stores the stale-based [1], discarding the completed push of 2. *)
  g_get_field "Hc1" "Ht". g_cas_succ "Hc1" "Ht". g_unop "Hc1". g_if_false "Hc1". g_seq "Hc1".
  iApply (goal_onecall_ret ⊤ p' [] 1 §None%V _ with "Hc1 Htr"). iIntros "Hc1 Htr".

  (* tag=3: Pop -- pops the surviving [1]. *)
  iApply (goal_onecall_call ⊤ op #l gen p'1 [] (1+1+1) §Pop%V _ goal_gen_pop with "Hc3 Htr"). iIntros "Hc3 Htr".
  iEval (rewrite /op /key_buggy_stack٠op) in "Hc3". g_call2 "Hc3". g_match "Hc3".
  rewrite /key_buggy_stack٠pop. g_call "Hc3".
  g_get_field "Hc3" "Ht". g_match "Hc3".
  g_cas_succ "Hc3" "Ht". g_if_true "Hc3". g_block "Hc3".
  iApply (goal_onecall_ret ⊤ p'1 [] (1+1+1) (‘Some( #1 ))%V _ with "Hc3 Htr"). iIntros "Hc3 Htr".

  (* tag=4: Pop -- the stack is empty: [2] was lost, although its push had
     completed before either pop started. *)
  iApply (goal_onecall_call ⊤ op #l gen p'2 [] (1+1+1+1) §Pop%V _ goal_gen_pop with "Hc4 Htr"). iIntros "Hc4 Htr".
  iEval (rewrite /op /key_buggy_stack٠op) in "Hc4". g_call2 "Hc4". g_match "Hc4".
  rewrite /key_buggy_stack٠pop. g_call "Hc4".
  g_get_field "Hc4" "Ht". g_match "Hc4".
  iApply (goal_onecall_ret ⊤ p'2 [] (1+1+1+1) §None%V _ with "Hc4 Htr"). iIntros "Hc4 Htr".

  iApply (Trace_fulfill with "Hrem Htr").
Qed.
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
- `‘Foo( e )` and `’Foo( v )` both parse in `val_scope` (`%V`) and mean the
  same value: when two identical-looking constructors refuse to unify, the
  suspect is the scope (`%V` vs `%E`), not the glyph. A location
  in a value list needs `%V` too: `l ↦∗ [(#c)%V]`.
- `§Foo` is a nullary tag; the empty list is `[]` (no `§[]`), cons is
  `x :: xs`. Tags compare by *index* only (`in_type _ n := n`): the
  program's `‘Push( #1 )` (tags in the case's `__types.v`) and the model's
  `‘SPush( #1 )` (tags in `pure_logic/<model>.v`) are the same value, so the
  trace may use either spelling.

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
| `nondet_bool ()` | a call | `goal_rand` by hand (§5) |
| `array٠init #n (fun: <> => ref v)` | a call | `goal_array_init_blk` by hand (§5) |

Plus `g_focus efoc "Hp"` (fold a context onto `ks`, no step), and `g_args "Hp"`
(= `repeat g_binop` then `g_znorm`, which computes closed integer
literals). The `g_array_*` tactics find the first fully-applied
`array٠get`/`set` on the spine and discharge both bounds by `lia`.

**Trace and adequacy.**

| | |
|---|---|
| `running 0 (most_general_client init op gen) -∗ Trace [] -∗ remaining (Trace T) -∗ goal ⊤` | driving obligation handed out by `mgc_non_lin_adequacy` (Theorem 2's `apply`, then `intros Σ hG. iIntros "Hrun Htr Hrem"`) |
| `goal_onecall_call ⊤ op obj gen pK [] i req _ goal_gen_r with "HcK Htr"` | runs `gen` through the driver, emits `Call req`, parks the thread on `op obj req` |
| `goal_onecall_ret ⊤ pK [] i resp _ with "HcK Htr"` | emits `Ret resp` from the bare return value |
| `Trace_fulfill with "Hrem Htr"` | closes Theorem 2 once `Htr : Trace T` |
| `is_non_linearizable_check_sound` + `solve_call_valid` + `per_tag_complete` | Theorem 1 (§6) |

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
   expression; `shape` is the lemma's argument with holes, e.g. `(array٠init _ _)%E`.
   Where the lemma takes `ks`, pass the context list instead:
   `(CtxIf _ _ :: ks)` inside a `goal_gen_*` driver, `[CtxIf _ _]` for
   thread 0 at the client's coin flip, `[]` for a forked thread at top
   level.
3. **Pass `_`** for everything the term fixes (`E`, `op`, `gen`, `ts`, the
   `obj` once read off the goal); supply only your choices (the coin
   `true`/`false`, the tag index as printed, the request or response value,
   the `goal_gen_*` driver).
4. **Goal order.** Coq premises first (`; first lia` for a bound), then one
   goal per `[…]` in the `with` pattern in order, then the continuation.
5. **Afterwards**, `iSimpl in "H"` before the next pure step: a hand
   application leaves `fill K (Val v)` unsimplified.

---

## 6. Witness trace design

A trace is a `list (positive * trace)` of `Call v` / `Ret v'` events, the
`positive` being the per-operation tag; the checker inserts the `Lin` events
itself. Requests are the tagged constructors `op` dispatches on (one per
public method, arguments inline); responses are option-wrapped so command
and query branches share a type: a unit-returning method answers `§None`, a
value-returning one `‘Some( v )` (or `§None` when empty), a boolean method
`ValBool b`.

**The reorderability rule.** A "spurious" response (a query returning empty
when the structure seems non-empty, a lost update, a duplicated value) is
non-linearizable **only if no real-time order justifies it**. A pending
(invoked-but-not-returned) operation may linearize anywhere up to its
response — or not at all — so a spurious response is reorderable, hence
*linearizable*. To witness the bug you need a **completed**
operation (its `Ret` precedes the offending `Call`) to *force* the state:
that real-time edge is what no reordering can break.

Write the trace, then the two pure lemmas of §3 (`per_tag_complete`, one
`destruct (decide (τ = …))` block per tag, and the
`is_non_linearizable_check_sound` theorem); `solve_call_valid` discharges
that every `Call` carries a valid request, and `by vm_compute` is the oracle. If
it fails (the checker computes `true`), the trace **is** linearizable:
redesign it, do not touch the checker.

**`gen`** is a coin-flip cascade over exactly the request values the trace
uses, and each request gets one `goal_gen_*` driver choosing the flips (§3);
`goal_onecall_call` takes the driver as its function argument. A driver for a
nullary request ends after its last `g_if_*` (nothing to `g_block`).

---

## 7. API card

<!-- API CARD: generated by gen_api_card.py, do not edit -->

`src/stdlib/rand.v`

```coq
Lemma goal_rand E p ks (b:bool) :
  focused p ks (nondet_bool (Val ValUnit)) -∗
  (focused p ks (Val (ValBool b)) -∗ goal E) -∗
  goal E.
```

`src/logic/most_general_client.v`

```coq
Lemma goal_onecall_call E (op obj gen : val) pk ks (i : Z) (v : val) ts :
  (∀ E' pp ks', running pp (fill ks' (gen (Val ValUnit))) -∗
                (running pp (fill ks' (Val v)) -∗ goal E') -∗ goal E') →
  running pk (fill ks (onecall_clo op obj gen (Val (ValInt i)))) -∗
  Trace ts -∗
  (running pk (fill (CtxLet "r" (emit #i (mkRet "r")) :: ks)
                    (App (App (Val op) (Val obj)) (Val v))) -∗
   Trace (ts ++ [(Z.to_pos i, Call v)]) -∗ goal E) -∗
  goal E.
```

`src/logic/most_general_client.v`

```coq
Lemma goal_onecall_ret E pk ks (i : Z) (r : val) ts :
  running pk (fill (CtxLet "r" (emit #i (mkRet "r")) :: ks) (Val r)) -∗
  Trace ts -∗
  (running pk (fill ks Unit) -∗ Trace (ts ++ [(Z.to_pos i, Ret r)]) -∗ goal E) -∗
  goal E.
```

`src/logic/most_general_client.v`

```coq
Lemma Trace_fulfill T :
  remaining (Trace T) -∗ Trace T -∗ goal ⊤.
```

`src/logic/adequacy_lin.v`

```coq
Lemma mgc_non_lin_adequacy `{M : model} (prog : expr) (T : list (positive * trace)) :
  trace_non_linearizable T →
  (∀ Σ (hG : seqlogGS Σ),
     running 0 prog -∗ Trace [] -∗ remaining (Trace T) -∗ goal ⊤) →
  ∃ c κ,
    wf_access.traced_steps ([prog], initial_state ValUnit) κ c ∧
    decode_trace κ = T ∧
    trace_non_linearizable (decode_trace κ).
```

`src/pure_logic/linear.v`

```coq
Definition per_tag_complete (ts : list (positive*trace)) :=
  ∀ τ, ∃ v v',
    filter (λ t, t.1 = τ) ts = [] ∨
    filter (λ t, t.1 = τ) ts = [(τ,Call v); (τ,Ret v')].
```

`src/pure_logic/linear.v`

```coq
Definition trace_non_linearizable `{M : model} ts :=
  call_valid ts ∧ ¬ trace_linearizable ts.
```

`src/pure_logic/linear_check.v`

```coq
Theorem is_non_linearizable_check_sound ts :
  call_valid ts →
  per_tag_complete ts →
  is_linearizable_check ts = false →
  trace_non_linearizable ts.
```

`src/linearizable/support/htbl_array.v`

```coq
Lemma goal_array_init_blk E p ks (n : nat) (v : val) :
  (0 < n)%nat →
  running p (fill ks ((array٠init #n (fun: <> => ref v))%E)) -∗
  (∀ (arr : location) (cells : list location),
     ⌜length cells = n⌝ -∗
     arr ↦ₕ□ Header 0 n -∗
     ([∗ list] i ↦ c ∈ cells, (arr +ₗ Z.of_nat i) ↦ ValLoc c) -∗
     ([∗ list] c ∈ cells, c ↦∗ [v]) -∗
     running p (fill ks (Val (ValLoc arr))) -∗ goal E) -∗
  goal E.
```

`src/logic/interp.v`

```coq
Lemma mz_pointsto_ne l1 dq1 v1 l2 dq2 v2 :
  l1 ↦{dq1} v1 -∗ l2 ↦{dq2} v2 -∗ ⌜l1 ≠ l2⌝.
```

<!-- END API CARD -->
