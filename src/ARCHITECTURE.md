# Architecture of `src/`

Mizzle is an **incorrectness** program logic built on Iris, targeting a
low-level model of concurrent OCaml, defined in `lang/`. Where a correctness
logic proves *all* executions are good, Mizzle proves *one* execution is bad:
it is an existence engine for a single witnessing interleaving.

The central object is the opaque proposition **`goal ⊤`**. A bug proof reduces
to establishing `goal ⊤` from thread tokens and a *remaining* obligation:

```coq
Lemma has_a_bug p ks e :
  remaining is_stuck' -∗ focused p ks e -∗ goal ⊤.
```

- `focused p ks e ≜ running p (fill ks e)` — thread `p` runs `e` under
  evaluation context `ks`.
- `remaining R` — the residual proof obligation is `R` (e.g. `is_stuck'`,
  `is_racy'`, or a non-linearizability witness); discharged once the chosen
  execution reaches the bad configuration.
- Driving the proof *is* scheduling: you hold several `running p` tokens and
  choose which to step next.

## Dependency layers (bottom → top)

```
lang/ (core) ──→ logic/ (core) ──→ stdlib/ ──→ logic/ (adequacy, completeness, MGC) ──→ benchmark solutions
     │                                              ↑         │
     └────────────→ pure_logic/ ────────────────────┘         └──→ lang/ instrumentation
lib/ ──→ pure_logic/, stdlib/
```

- `stdlib/` specs are stated in goal mode, so every `stdlib/` file sits on
  top of the core of `logic/`.
- `logic/most_general_client.v` uses `stdlib/rand`, and it,
  `adequacy_lin.v` and `completeness_lin.v` use `pure_logic/linear`.
- The three instrumentation files of `lang/` (`alt_semantics.v`,
  `locs_in_headers.v`, `block_heap_complete_preserved.v`) import
  `logic/` (`decompose`, `wf_access`, `interp`, `translate`, `completeness`),
  so they sit above it despite their location.

## Import preludes

Rather than repeat the iris/lang/mizzle import incantation at the top of every
file, the common sets are factored into `Require Export` **prelude** files,
layered so each benchmark adds only what it needs on top of a shared core:

```
logic/prelude.v                     core: iris proof mode + lang syntax + goal logic & g_* tactics
  ├─ linearizable/support/mgc_prelude.v   + most_general_client, adequacy_lin, linear[_check], rand, atomic_loc
  │    └─ linearizable/support/htbl_prelude.v  + htbl_model, stdlib assume/array, htbl_array
  ├─ dataracebench/support/drb_prelude.v  + race, adequacy, structeq, drb_axiom, atomic_loc, options
  └─ test/test_prelude.v              + stuck
```

A solution file then opens with one prelude `Require Import` plus only its
case-specific requires (the data-structure model and the case's
`__code`/`__types`). Three ordering facts the preludes bake in: only
`lang/syntax` is needed by name — the tactic/typeclass instances of
`lang/instances` register transitively; a `stdlib` `structural_equality`
import must precede the mizzle notations, or its `=` shadows mizzle's; and
`lang/options` goes **last** in a require block, since it
overrides stdpp tactics of the same name (this is why every language-core
file of `lang/` ends its block with it).

## `lang/` — the language

`syntax.v` / `semantics.v` / `instances.v` define the language, resting on
the support layer `prelude.v` / `options.v` / `classes.v` / `list.v`. The
other three files are Mizzle's own instrumentation on top.

Two features are specific to the logic's needs:

- Field accesses are `GetField atm` / `SetField atm`, with
  `atm : atomicity` (`Atomic` / `NotAtomic`). The flag does not change the
  step (the semantics is an SC interleaving) and exists only for
  `logic/race.v`.
- `Emit e` steps to `()` and appends the value to the observation trace
  threaded by `prim_step` / `nsteps`.

| File | Purpose |
|------|---------|
| `prelude.v` | `ssreflect` + stdpp re-export, the `￢` / `₊` notations, the `nat → Z` coercion. |
| `options.v` | The tactic overrides (`done`, `simplify`, `invert`, `destruct_decide`) and the ambient flags. **Import last.** |
| `classes.v` | `Similar` / `Nonsimilar` (`≈`, `≉`), `Beq` (`≟`) and their instances; re-exported by `syntax.v`. |
| `list.v` | `simpl_length`, the index-passing folds `foldri` / `foldr2`, and the `Prop`-valued `Foralli` / `Forall2'`. |
| `syntax.v` | Locations, the `expr` / `val` AST (with `atomicity` and `Emit`), substitution, states, physical equality, and all the surface notations. |
| `semantics.v` | `base_step` (with observations), evaluation contexts and the `Context` class, `AsVal`, `prim_step`, `step` / `nsteps`, reducibility and the `fill` metatheory. |
| `instances.v` | `reshape_expr`, the `mizzle_simplify` / `invert_base_step` tactics, the `AsVal` / `AsValRec` / `AsValRecs` / `AsValRecs'` instances, and the `PureExec` instances (`pure_*`). |
| `alt_semantics.v` | Bound-checked small-step semantics (`base_step_bc` / `prim_step_bc` / `silent_step_bc`): every mutable field op additionally requires the field to be in bounds. Proven equivalent to `logic/wf_access.v`'s `step` (`prim_step` refined by `wf_access`). |
| `locs_in_headers.v` | `wf_header`: ops whose `ValLoc` base must be a real header base in the state for the source side to step. |
| `block_heap_complete_preserved.v` | Invariant `block_heap_complete` (every allocated block fills its heap range) and its preservation under stepping. |

## `logic/` — the program logic

**Core / definitions**

| File | Purpose |
|------|---------|
| `decompose.v` | Pure evaluation-context machinery: `split_block` (rightmost non-value, right-to-left block order), `decompose_step`, `decompose` (context/redex split). |
| `wf_access.v` | `wf_access σ e`: the next redex is not an out-of-bounds field access. Vacuous on non-field redexes. |
| `negation.v` | `neg P := P → False`, plus the ghost-algebra lemmas for points-to *disagreement* (contradiction from conflicting fragments). |
| `interp.v` | Ghost state class `seqlogGS` (heap, headers, split map, locals, saved props, location set, observation trace) and the state interpretation. |
| `goal.v` | The `goal` fixpoint (the incorrectness WP-analog), its stepping lemmas (incl. `goal_emit`), and `wf_*` discharge tactics. |
| `goal_proof.v` | The `focused p ks e` notation and the focused restatement of every `goal` lemma (`focused_bind`, `focused_*_at`, …). |
| `goal_tactics.v` | Ltac tactics that look up a `focused` hypothesis, `reshape_expr` its redex, and apply the matching stepping lemma — no `ks` bookkeeping. |
| `wp.v` | A WP over `running` threads (`wp p e Q`), with evaluation-context support for `wp_bind`. |
| `wp_goal.v` | Running a `wp` inside `goal`: `wp_run_at`. |
| `prelude.v` | The shared **import prelude**: `Require Export`s iris proof mode, `lang/syntax` (instances arrive transitively), and `interp`/`goal`/`goal_proof`/`goal_tactics`. Every proof builds on this instead of hand-writing the import block (see *Import preludes* above). |

**Remaining-obligation predicates**

| File | Purpose |
|------|---------|
| `stuck.v` | `Stuck es σ` (some thread irreducible ignoring OOB) and `is_stuck'`. |
| `base_stuck.v` | `base_stuck`: enumerates every reason a `base_step` cannot fire under `wf_access`. |
| `race.v` | `local_access` / `access` (GetField/SetField/CAS/Xchg/FAA to `l +ₗ fld`, carrying an `access_kind` = write flag × atomicity), `races` (a race needs a write *and* a non-atomic participant), `is_racy` / `is_racy'`, `is_racy_intro`, and the `solve_access` / `solve_races` tactics. |

**Adequacy — extract a real execution from `goal`**

| File | Purpose |
|------|---------|
| `adequacy.v` | Trace-aware `goal_adequacy`: extracting the `goal` fixpoint yields a real reduction plus the observation trace `κ`. |
| `adequacy_stuck.v` | `goal_adequacy` specialized to `is_stuck'` / `Stuck` → a reachable stuck configuration. |
| `adequacy_lin.v` | Specialization producing a real reduction whose observation trace is non-linearizable. |

**Completeness / translation**

| File | Purpose |
|------|---------|
| `translate.v` | The ψ-translation: a `gmap location location` bijection applied pointwise to expressions, values and evaluation contexts (`tr_loc`, `tr_expr`, `tr_val`, `tr_ectx`, …). |
| `completeness.v` | Core completeness: the logic reproduces every real execution. |
| `completeness_stuck.v` | Completeness for stuckness (irreducible-redex normal form). |
| `completeness_race.v` | Source accesses translate to target accesses on the ψ-renamed expression (two threads race on `tr_loc ψ l`). |
| `completeness_lin.v` | `mirror` exposes the shadow observation trace; hooks the logic to (non-)linearizability of the emitted trace. |
| `most_general_client.v` | The most-general client: `init ()` then fork `nondet_bool`-many concurrent `op obj (gen ())`; `mkCall`/`mkRet`/`emit`. |

## `pure_logic/` — sequential specs & linearizability (no program logic)

| File | Purpose |
|------|---------|
| `linear.v` | The linearizability framework (`model`, `trace_linearizable`, `adv_step`, …), retargeted from `heap_lang` to `lang/`. |
| `linear_check.v` | Decidable boolean `is_linearizable_check` (enumerate `Lin` permutations, run the model's executable `step`); soundness lemma. |
| `stack_model.v` | LIFO stack model (`SPush`/`SPop`). |
| `queue_model.v` | FIFO queue model, bare responses, blocking deq (`QEnq`/`QDeq`). |
| `queue_opt_model.v` | FIFO queue model, option responses (Michael–Scott queues). |
| `htbl_model.v` | Hash-table model with boolean responses (`HAdd`/`HRemove`/`HMem`). |
| `queue_check_test.v` | Smoke test that `vm_compute` reduces a known bad queue trace to `false`. |

## `lib/`

| File | Purpose |
|------|---------|
| `list.v` | Pure `stdpp` list auxiliaries (`substr`, `take_while`, extra `filter`/`Forall`/`list_find` lemmas). |
| `big_sepL.v` | `big_sepL`/`replicate` lemmas (`big_sepL_replicate`, `_1`, `_2`) for `stdlib/array.v`. |

## `stdlib/` — the OCaml standard library

Each file holds, in this order, the **program text** of one primitive and its
**goal-mode specs**, so benchmark proofs can step through library calls; the
definitions are sealed `#[global] Opaque` at the end of the file, once the
specs are proven. Exceptions: `rand.v` leaves `nondet_bool` unsealed, and
`structeq` is sealed in `structural_equality.v` and made `#[local]
Transparent` again in `structeq.v` for its specs. Generated code requires these same files (`ocaml2mizzle`
emits `mizzle.stdlib` requires), so a case file pulls in the specs together
with the code.

`atomic_loc.v` holds split-argument forms of the read-modify-writes (see
below). `mutex.v`'s `lock` routes its CAS through `atomic_loc٠cas`, as
generated code does. `structural_equality.v` carries program text alone,
specced in `structeq.v`.

| File | Primitive |
|------|-----------|
| `assert.v` | `assert` (`if v then () else Fail`). |
| `assume.v` | `assume` and `diverge`. |
| `rand.v` | `nondet_bool` (fork-based nondeterminism). |
| `trace.v` | Append-only trace library (entries are `(positive label, value)` pairs). |
| `structeq.v` | `structeq` on integers (`focused_structeq_int` → `bool_decide (z1 = z2)`). |
| `array.v` | Arrays (`array.init`, `array.get`, …). |
| `dynarray_1.v` | Dynamic array `create`. |
| `mutex.v` | Mutexes (single boolean cell). |
| `condition.v` | Condition variables. |
| `ivar_2.v` | Write-once cell (`ivar`). |
| `domain.v` | `domain٠spawn` / `domain٠join`. |
| `atomic_loc.v` | `atomic_loc٠cas` / `٠xchg` / `٠faa` taking the target as location **and** field. |

### Atomic-location descriptors

`CAS` / `Xchg` / `FAA` take their target as one *descriptor*: the two-field
tuple representing OCaml's `Atomic.Loc.t`, which `e.[fld]` builds. The
semantics keeps that shape, because `ocaml2mizzle` passes descriptors around
first-class (`Atomic.Loc.compare_and_set loc v1 v2` translates to a `CAS`
whose first operand is a plain variable), so splitting the primitives would
lose `Atomic.Loc.t` support.

Written in source form the descriptor is a `Block` *expression*, so it must be
reduced to a value before the rules of `logic/goal.v` apply — which is awkward
when you want to *apply a spec* rather than script tactics.

`stdlib/atomic_loc.v` therefore provides split-argument wrappers taking
the location and the field separately, with `⟨fld⟩` naming a field on its own
(field names otherwise live in the `mizzle_field` custom entry and are only
reachable inside `.[ ]` / `.{ }` / `.< >`). `ocaml2mizzle` emits them **whenever
the descriptor is built at the call site**:

```coq
atomic_loc٠cas "t" ⟨contents⟩ !ᵃᵗ"t" "after"     (* Atomic.compare_and_set *)
CAS "loc" v1 v2                                  (* Atomic.Loc.compare_and_set:
                                                    an opaque descriptor came
                                                    in, nothing to split *)
```

The same file specs them — `focused_atomic_loc_cas_succ` /
`_cas_fail` / `_xchg` / `_faa`, plus `_at` variants under an evaluation
context — with the same side conditions and footprint as the `logic/goal.v`
rules, and with the descriptor reduction absorbed. (The names are deliberately
*not* `focused_cas_succ` and friends: those already exist in
`logic/goal_proof.v` for the primitives.)

For stepping proofs, `atomic_loc.v` defines `g_cas_succ` / `g_cas_fail`,
which fire on a wrapper call and otherwise on a primitive `CAS`. Without
`atomic_loc.v` in scope, only the primitive-only `g_cas_prim_succ` /
`g_cas_prim_fail` from `logic/goal_tactics.v` are available.

## `dataracebench/` — data-race benchmark (mode **DRB**)

- `cases/{drb,drbheld}NNN_*__code.v` — AST of each DataRaceBench case
  (generated by the vendored `ocaml2mizzle`, which emits `mizzle.lang` /
  `mizzle.stdlib` requires directly). `drbheld` cases are the held-out set
  (post-submission and lock-based ports).
- `support/` — hand-written support for the proofs:
  - `support/drb_axiom.v` — axiomatized `drb٠parallel_for`,
    `drb٠parallel_for_chunked` and `array٠make_matrix`, with their specs.
  - `support/drb_prelude.v` — the DRB import prelude (see *Import preludes*).
  - `support/drb_axiom_realize.v` — plain-language realization of the
    `drb_axiom` primitives (divide-and-conquer `parallel_for`,
    one-domain-per-chunk `parallel_for_chunked`, row-by-row `make_matrix`).
  - `support/PROOF_GUIDE.md` — the proof guide.
- `solutions/{drb,drbheld}NNN_*__proof.v` — solution proofs (each shows the
  case is racy), written by an agent during a benchmark run.

## `linearizable/` — linearizability benchmark (mode **NonLin**)

- `cases/linNNN_*__code.v`, `cases/key_buggy_stack__code.v` — AST of each
  structure (Treiber stacks, Michael–Scott queues, hash tables), generated by
  the vendored `ocaml2mizzle`. `__types.v` carry variant-tag notations.
- `support/` — hand-written support for the proofs:
  - `support/mgc_prelude.v`, `support/htbl_prelude.v` — the import preludes
    (see *Import preludes*).
  - `support/htbl_array.v` — the two array ops the hash-table witnesses need,
    proven over `stdlib/array` (no array-specific axiom).
  - `support/PROOF_GUIDE.md` — the proof guide.
- `solutions/linNNN_mgc.v`, `solutions/key_buggy_stack_mgc.v` — solution
  proofs via the most-general client (one `model` instance + a
  `trace_non_linearizable` witness per example), written by an agent during a
  benchmark run.

## `test/`

Standalone examples / smoke tests (`race*`, `seq*`, `hw*`, `counter`,
`negate1`, `while1`), not part of the benchmark suites. `test_prelude.v` is their shared
import prelude (see *Import preludes*).
