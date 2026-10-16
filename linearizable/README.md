# linearizable — concurrent stack, queue, hash-table & list variants

OCaml source for families of lock-free data structures used as input to
`ocaml2mizzle`, which produces the Mizzle Rocq embedding under
`../src/linearizable/`. This project mirrors the layout of the
sibling `dataracebench` project: the translatable sources live in `bin/`
(library `cases`), and `gen_mizzle.sh Lin` (in `..`) emits the
generated Rocq into `../src/linearizable/cases/`.

Each `bin/lin0NN_*.ml` exposes one data structure behind a single operation
`op t req`:

- **Treiber stacks** (`lin001`–`lin005`) dispatch on `Push x` / `Pop`,
  matching the sequential spec in `../src/pure_logic/stack_model.v`
  (`Push x` pushes and returns `None`; `Pop` returns `Some top` or `None`).
- **Michael-Scott queues** (`lin006`–`lin010`) dispatch on `Enq x` / `Deq`
  against a FIFO model (`Enq x` enqueues and returns `None`; `Deq` returns
  `Some front` or `None`).
- **Hash tables** (`lin011`–`lin015`) dispatch on `Add (k, v)` / `Remove k` /
  `Mem k`, each returning a `bool`, against a finite-map model (`Add` returns
  whether the key was absent and thus inserted; `Remove` whether it was
  present and thus deleted; `Mem` whether it is present).

`bin/key_buggy_stack.ml` is the buggy Treiber stack of the paper's key-ideas
section (fig-buggy-stack): `push` CASes against a freshly re-read head rather
than the snapshot it built on (the same mutation as `lin003`).

The variants are deliberately buggy: each applies one small mutation to the
classic lock-free algorithm that makes it **non-linearizable** under
concurrency. (`bin/` is a translation library only — each file defines the
operations but no executable entry point.) Correct ports, restricted to the
same ocaml2mizzle-translatable subset, live in the sibling `orig` library (`treiber_stack.ml`, `michael_scott_queue.ml`,
`htbl.ml`, and `two_lock_queue.ml`, `harris_list.ml` for the held-out set).

The **held-out set** (`bin/linheld0NN_*.ml`, like `drbheldNNN` for
DataRaceBench) uses two algorithms the guide never shows:

- **Two-lock queues** (`linheld016`–`linheld019`) dispatch on `Enq x` / `Deq`
  against the same FIFO model as the Michael-Scott queues, and synchronize
  through `Mutex` (`src/stdlib/mutex.v`), which the guide does not cover.
- **Harris lists** (`linheld020`–`linheld023`) dispatch on `Add (k, v)` /
  `Remove k` / `Mem k` against the same finite-map model as the hash tables
  (no operation returns a value, so the model is a set in practice).

The sources are an ocaml2mizzle-compatible subset of OCaml (no exceptions, GADTs, or
nested modules).

## Build

```sh
dune build
```

## Treiber stack variants

`push`/`pop` are the two stack operations; the correct algorithm reads the
head, then commits with a `compare_and_set` (CAS) that both validates the head
is unchanged and retries on failure.

| OCaml file                      | Mutation                                                        | Non-linearizable behavior |
|---------------------------------|-----------------------------------------------------------------|---------------------------|
| `bin/lin001_treiber_stack1.ml`  | `push` reads then stores (`set t (v :: get t)`) — no CAS        | Concurrent pushes both read the same head and the second store overwrites the first: a pushed element is **lost** (data race). |
| `bin/lin002_treiber_stack2.ml`  | `pop` reads the head then stores the tail — no CAS             | Concurrent pops both read the same head, both store the tail, both return it: an element is **popped twice** (data race). |
| `bin/lin003_treiber_stack3.ml`  | `push` CASes against a freshly re-read head, not the read it built on | The CAS no longer validates the snapshot it used, so a concurrent push in between is **lost** (data race). |
| `bin/lin004_treiber_stack4.ml`  | `push` performs the CAS but does not retry on failure          | On contention the CAS fails and `push` returns anyway: the element is **lost**, yet the operation reports completion. No data race — all accesses are atomic. |
| `bin/lin005_treiber_stack5.ml`  | `pop` performs the CAS but returns `None` on failure instead of retrying | On contention `pop` returns `None` (claiming empty) though the stack was never empty during the call. No data race — all accesses are atomic. |

## Michael-Scott queue variants

Nodes are `Nil | Next of 'a * 'a node Atomic.t`; `head`/`tail` are atomic
pointers to cells. The correct algorithm advances `head` with a CAS to
dequeue, links a new node into the open (`Nil`) tail cell with a CAS — relinking
via a walk to the true end on contention — and then lazily swings `tail`.

| OCaml file                    | Mutation                                                          | Non-linearizable behavior |
|-------------------------------|-------------------------------------------------------------------|---------------------------|
| `bin/lin006_ms_queue1.ml`     | `pop` (deq) returns `None` on CAS failure instead of retrying     | On contention `pop` returns `None` (claiming empty) though the queue was never empty during the call. |
| `bin/lin007_ms_queue2.ml`     | `pop` advances `head` with a plain store — no CAS                 | Concurrent pops both read the same head and both return its element: a logical element is **dequeued twice** (data race). |
| `bin/lin008_ms_queue3.ml`     | `pop`'s CAS validates a freshly re-read `head`, not the snapshot it read the node from | The CAS no longer validates that snapshot, so the head can advance underneath it: **duplicate dequeue**. |
| `bin/lin009_ms_queue4.ml`     | `push` (enq) drops the relink fallback (`find_tail_and_enq`)      | A contended enqueue's node is never linked: the element is **lost**, yet the operation reports completion. |
| `bin/lin010_ms_queue5.ml`     | `pop` reads the value via a separate `peek` from the CAS that removes the node | If `head` advances between the `peek` and the CAS, the returned value and the removed element differ: **duplicate and loss simultaneously**. |

## Hash table variants

Buckets are a fixed array of 16 `Atomic.t` cells
(`Array.init 16 (fun _ -> Atomic.make Nil)`), each holding an immutable
association list (`Nil | Cons of int * int * bucket`); keys hash by identity
and `key land 15` selects the bucket. The correct algorithm
reads a bucket, decides from that snapshot, and commits with a single
`compare_and_set` that re-validates the snapshot — so the membership/rebuild
decision and the write are atomic together. Each variant breaks that link in
one place. (Witnesses contend on a single bucket via colliding keys — equal modulo 16,
e.g. 1 and 17 — or the same key.)

| OCaml file                | Mutation                                                                  | Non-linearizable behavior |
|---------------------------|---------------------------------------------------------------------------|---------------------------|
| `bin/lin011_htbl1.ml`     | `try_add` commits with a plain store instead of a CAS                     | Concurrent adds to one bucket both read the same spine and the second store overwrites the first: an inserted key is **lost**, yet both `Add`s report `true` (data race). |
| `bin/lin012_htbl2.ml`     | `try_remove` commits with a plain store instead of a CAS                  | Concurrent removes from one bucket clobber each other: a key whose `Remove` returned `true` is **still present** (data race). |
| `bin/lin013_htbl3.ml`     | `try_add`'s CAS validates a freshly re-read bucket, not the snapshot it built the new spine on | A concurrent insert in between is **lost** — its node is dropped when the stale spine is reinstalled (data race). |
| `bin/lin014_htbl4.ml`     | `try_add` returns `true` on CAS failure instead of retrying              | On contention `Add` reports success but **never inserts** the key. No data race — all accesses are atomic. |
| `bin/lin015_htbl5.ml`     | `try_add` checks membership on one read but builds/CASes from a later re-read | A concurrent add of the *same* key slips between the two reads, so the key is inserted **twice** — a duplicate binding a map can never hold. |

## Held-out: two-lock queue variants

The two-lock queue of Michael and Scott (PODC 1996) uses the same cells as
the Michael-Scott variants (`Nil | Next of 'a * 'a node Atomic.t`), with
`head`/`tail` pointers to cells. Enqueues serialize on `tail_lock`: read
`tail`, link the new node into that cell, move `tail`. Dequeues serialize on
`head_lock`: read the front node and move `head` past it. When the queue is
empty an enqueue and a dequeue touch the same cell, so cells and pointers are
atomic although every write happens under a lock. No witness needs a thread
to block on a held lock: the mutex specs only cover locking a free mutex.

| OCaml file                         | Mutation                                                              | Non-linearizable behavior |
|------------------------------------|-----------------------------------------------------------------------|---------------------------|
| `bin/linheld016_two_lock_queue1.ml` | `push` takes no lock                                                 | Two enqueues read the same `tail` cell and the second link overwrites the first: an element is **lost**. |
| `bin/linheld017_two_lock_queue2.ml` | `pop` reads `head` before taking `head_lock`                         | A dequeue holding a stale `head` dequeues the node a concurrent dequeue already returned: **duplicate dequeue**. |
| `bin/linheld018_two_lock_queue3.ml` | `push` moves `tail` and releases the lock before linking its node    | A later enqueue links behind a node that is not linked yet. A dequeue sees an empty queue although that later enqueue has **completed**: spurious empty. |
| `bin/linheld019_two_lock_queue4.ml` | `pop` reads the front in one critical section and moves `head` in a second one | Two dequeues return the same front, and the second one moves `head` past the next node too: **duplicate and loss**. |

## Held-out: Harris list variants

A sorted lock-free linked list (Harris, DISC 2001, with Michael's helping
traversal, SPAA 2002). Each node is its `next` cell, of type
`link Atomic.t` with `link = Nil | Cons of int * int * link Atomic.t | Marked
of link`: the cell holds the successor, or `Marked succ` once the node is
logically deleted. Removal first marks the node (CAS on its cell), then
unlinks it (CAS on its predecessor's cell); since the mark lives in the same
atomic word as the successor, an insertion after a marked node fails its
CAS. `find` unlinks marked nodes it meets and restarts if its predecessor is
marked.

| OCaml file                       | Mutation                                                             | Non-linearizable behavior |
|----------------------------------|----------------------------------------------------------------------|---------------------------|
| `bin/linheld020_harris_list1.ml` | `remove` unlinks with one CAS on the predecessor, without marking   | A key inserted right after the removed node is unlinked with it: a completed `Add` is **lost**. |
| `bin/linheld021_harris_list2.ml` | `mem` walks the list without checking the found node's mark          | A `Remove` that marks but fails to unlink (its predecessor changed) returns `true`, yet a later `Mem` still finds the key: **removed key visible**. |
| `bin/linheld022_harris_list3.ml` | `remove` ignores the result of the marking CAS                       | Two `Remove`s of one key both return `true`: **duplicate remove**. |
| `bin/linheld023_harris_list4.ml` | a failed insertion CAS is retried on the same predecessor, without a new `find` | If the predecessor was deleted meanwhile, the retry links the node into the unreachable deleted node: a completed `Add` is **lost**. |
