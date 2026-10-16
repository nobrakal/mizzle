# DataRaceBench — OCaml translations

An adaptation of the [DataRaceBench](https://github.com/LLNL/dataracebench)
suite: OCaml 5 translations of a selection of "yes" (racy) DataRaceBench
micro-benchmarks.

OpenMP has no direct OCaml equivalent, so the OpenMP constructs are mapped
onto [Domainslib](https://github.com/ocaml-multicore/domainslib) task pools
(and OCaml 5's [`Domain`](https://ocaml.org/manual/parallelism.html) module
for `Drb.par`) via the shared helpers in `lib/drb.ml`:

- `Drb.parallel_for` — `#pragma omp parallel for`: runs the iterations as
  Domainslib work-stealing chunks over a pool of domains, with an implicit
  barrier at the end — and, like OpenMP, no synchronisation between
  iterations.
- `Drb.parallel_for_chunked` — `schedule(static,c)`.
- `Drb.par` — a two-thread parallel region (or `parallel sections` with two
  sections): runs its two arguments in two domains, then joins.

Plain `array` and `ref` accesses are non-atomic across domains, so the
original data races carry over faithfully.

Translation conventions:

- the command-line override of `len` in the `-var` variants is dropped, the
  C default length is hard-coded instead;
- C `double`/`float` data is mapped to `int` (`0.5` init becomes `1`,
  `0.5*i` becomes `i`, float increments become the same integer increments);
- the final `printf` of the C originals is dropped: each benchmark is a pure
  racy computation with no observation code (no print or assert), except
  DRB185, which keeps the `assert` that is part of its synchronisation
  protocol;
- the out-of-bounds benchmarks (DRB014/015), whose race goes through a C
  negative-index read aliasing the previous row, flatten the 2-D array to a
  1-D array to reproduce the C memory layout within OCaml's array bounds;
- `#pragma omp simd` (DRB024) is mapped to `Drb.parallel_for`;
  `parallel for simd schedule(dynamic,64)` (DRB202–207) likewise, the
  schedule playing no role in the race;
- C loops starting at `1` and ending before `hi` are run as
  `Drb.parallel_for (hi - 1)` over `k`, with `i = k + 1` (`n - 1` in DRB014,
  `n - 2` in DRB195/197);
- `rand()` initial values are replaced by the constant `1`;
- C pointers into a buffer become integer offsets into one array, and 3-D
  arrays are flattened;
- C pointer variables that are reassigned become `ref`s holding arrays.

## Build

The benchmarks are compiled as a library (`cases`) intended for translation
to Rocq by `ocaml2mizzle`; each file defines a `main` function but no executable
entry point.

```sh
dune build
```

## Benchmarks

| OCaml file                          | Original C                            | Pattern |
|-------------------------------------|---------------------------------------|---------|
| `bin/drb001_antidep.ml`             | DRB001-antidep1-orig-yes.c            | loop-carried anti-dependence `a.(i)=a.(i+1)+1` |
| `bin/drb003_antidep2.ml`            | DRB003-antidep2-orig-yes.c            | 2-D anti-dependence on outer loop |
| `bin/drb005_indirectaccess1.ml`     | DRB005-indirectaccess1-orig-yes.c     | indirect index set, two bases 12 apart, `schedule(static,1)` |
| `bin/drb006_indirectaccess2.ml`     | DRB006-indirectaccess2-orig-yes.c     | same, default scheduling, patch at `indexSet[5]` |
| `bin/drb009_lastprivatemissing.ml`  | DRB009-lastprivatemissing-orig-yes.c  | missing lastprivate on shared `x` |
| `bin/drb011_minusminus.ml`          | DRB011-minusminus-orig-yes.c          | shared counter `numNodes2--` |
| `bin/drb014_outofbounds.ml`         | DRB014-outofbounds-orig-yes.c         | cross-row race via out-of-bounds read (flattened) |
| `bin/drb015_outofbounds_var.ml`     | DRB015-outofbounds-var-yes.c          | same, variable-length variant |
| `bin/drb016_outputdep.ml`           | DRB016-outputdep-orig-yes.c           | output + true dep on shared scalar `x` |
| `bin/drb018_plusplus.ml`            | DRB018-plusplus-orig-yes.c            | shared counter `out_len++` |
| `bin/drb020_privatemissing_var.ml`  | DRB020-privatemissing-var-yes.c       | missing private on shared `tmp` |
| `bin/drb024_simdtruedep.ml`         | DRB024-simdtruedep-orig-yes.c         | simd loop-carried true dependence |
| `bin/drb029_truedep1.ml`            | DRB029-truedep1-orig-yes.c            | loop-carried true dependence `a.(i+1)=a.(i)+1` |

### Post-submission ports (`drbheld`)

Ported after the proof guide was tuned on the cases above, as a held-out set.

| OCaml file                                 | Original C                               |
|--------------------------------------------|------------------------------------------|
| `bin/drbheld033_truedeplinear.ml`          | DRB033-truedeplinear-orig-yes.c          |
| `bin/drbheld037_truedepseconddimension.ml` | DRB037-truedepseconddimension-orig-yes.c |
| `bin/drbheld039_truedepsingleelement.ml`   | DRB039-truedepsingleelement-orig-yes.c   |
| `bin/drbheld111_linearmissing.ml`          | DRB111-linearmissing-orig-yes.c          |
| `bin/drbheld124_master.ml`                 | DRB124-master-orig-yes.c                 |
| `bin/drbheld160_nobarrier.ml`              | DRB160-nobarrier-orig-gpu-yes.c          |
| `bin/drbheld169_missingsyncwrite.ml`       | DRB169-missingsyncwrite-orig-yes.c       |
| `bin/drbheld179_threadsensitivity.ml`      | DRB179-thread-sensitivity-yes.c          |
| `bin/drbheld195_diffusion1.ml`             | DRB195-diffusion1-yes.c                  |
| `bin/drbheld197_diffusion2.ml`             | DRB197-diffusion2-yes.c                  |
| `bin/drbheld202_simdbroadcast.ml`          | DRB202-simd-broadcast-yes.c              |
| `bin/drbheld204_simdgather.ml`             | DRB204-simd-gather-yes.c                 |
| `bin/drbheld206_simdscatter.ml`            | DRB206-simd-scatter-yes.c                |
| `bin/drbheld207_simdloadstore.ml`          | DRB207-simd-loadstore-yes.c              |

DRB124 and DRB160 are two-thread programs written with `Drb.par`:

- `omp master` is the calling (second) thread of `Drb.par`; it has no
  implicit barrier, so the other thread reads `init` concurrently with the
  master's write (DRB124);
- in DRB160, the number of teams and the `distribute` schedule are
  implementation defined: the port fixes two one-thread teams with a static
  block distribution of the iterations. As there is no barrier between the
  two `distribute` loops, each team runs its block of both loops in one
  `Drb.par` branch; mapping each loop to a `Drb.parallel_for` would add the
  missing barrier and remove the race. The `target`/`map` offloading is
  dropped (one shared memory), as is the final check.

### Lock ports (`drbheld`)

"yes" benchmarks whose synchronisation uses locks (`omp_set_lock` /
`omp_unset_lock`, or `omp critical`), restricted to those whose race is
observable under sequential consistency. All of them are two-thread programs,
written with `Drb.par` (`Domain.spawn` + `Domain.join`).

Additional translation conventions:

- OpenMP locks are `Mutex.t`s, a nest lock that is only taken once (DRB119)
  being a plain mutex;
- a parallel region with two threads is a `Drb.par`, with an implicit
  barrier at its end;
- a leading `omp barrier` with nothing but thread-local code before it in
  the parallel region is dropped; any other `omp barrier` splits the region into consecutive
  `Drb.par` phases, locks staying held across phases (DRB187/189). Since a
  lock may then be released by a different domain than the one that took
  it, these ports would raise at run time with OCaml's error-checking
  `Mutex`; they are only meant for translation.
- `omp flush` is a no-op under sequential consistency and is dropped, and a
  `reduction(+:sum)` becomes one private sum per thread, added up after the
  join (DRB074);
- an unnamed `omp critical` is one mutex shared by the whole program; each
  named `omp critical(X)` is a distinct mutex, so differently named critical
  sections do not exclude each other (DRB191/193);
- busy-waiting `while` loops are kept as OCaml `while` loops, and C integer
  `done` flags become `bool` refs (named `fin`, `done` being an OCaml keyword);
- a `firstprivate` variable becomes a `ref` local to each thread (DRB191).

| OCaml file                                 | Original C                          | Race |
|--------------------------------------------|-------------------------------------|------|
| `bin/drbheld074_flush.ml`                 | DRB074-flush-orig-yes.c             | `i := 1` under the lock vs. the unprotected read of `i` |
| `bin/drbheld119_nestlock.ml`              | DRB119-nestlock-orig-yes.c          | `b` incremented under the lock vs. without it |
| `bin/drbheld185_barrier1.ml`              | DRB185-barrier1-yes.c               | `x := 0` vs. `x := 1`: each thread raises and lowers its own flag, so the flag barrier never synchronises |
| `bin/drbheld187_barrier2.ml`              | DRB187-barrier2-yes.c               | `x := 0` vs. `x := 1`: the lock handoff is not a barrier |
| `bin/drbheld189_barrier3.ml`              | DRB189-barrier3-yes.c               | `x := 0` vs. `x := 1`: lock-based barrier with one synchronisation missing |
| `bin/drbheld191_criticalsection2.ml`      | DRB191-critical-section2-yes.c      | `size` incremented in `critical(A)` vs. read and decremented in `critical(B)` |
| `bin/drbheld193_criticalsection3.ml`      | DRB193-critical-section3-yes.c      | `s := 1` in `critical(A)` vs. the read of `s` in `critical(B)` |
| `bin/drbheld201_sync1.ml`                 | DRB201-sync1-yes.c                  | `x := 0` inside the lock vs. `x := 1` after a lock/unlock |
