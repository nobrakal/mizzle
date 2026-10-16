"""Shared name/family metadata for the benchmark cases.

Single source of truth for the code -> (family, bug description) mapping used by
the replay harness (replay.py).
DRB_META covers both the DRB (drbNNN) and the held-out DRBheld (drbheldNNN)
cases, and LIN_META both the Lin (linNNN) and the held-out Linheld
(linheldNNN) cases; the modes are told apart by their code prefix.
"""

# DRB code -> (family, qualitative data-race description)
#
# Families group by the *mechanism* of the race, not the shape of the fix:
#   - "Loop-carried": in a parallel loop, iteration i conflicts with a specific
#     other iteration determined by the index expressions: a fixed stride
#     (anti / true / output deps; drb014/015 are cross-row neighbour deps
#     spelled with a -1; aliased or overlapping buffers only set up such a
#     dependence), an affine index, or an index array (drb005/006).
#   - "Shared cell": in a parallel loop, every iteration hits the same shared
#     cell or scratch array, with no ordering (shared counters, missing
#     privatization, one element written by one iteration and read by all).
#   - "Missing sync.": two threads (Drb.par) whose synchronization is absent
#     or does not order the conflicting accesses (missing barrier, access
#     outside the lock, distinct locks, broken hand-rolled barriers).
#
# Descriptions say what the OCaml port does, not which OpenMP construct the
# original DataRaceBench program is missing.
DRB_META = {
    "drb001": ("Loop-carried", "Write-after-read"),
    "drb003": ("Loop-carried", "Write-after-read (2D loop)"),
    "drb024": ("Loop-carried", "Read-after-write (two arrays)"),
    "drb029": ("Loop-carried", "Read-after-write"),
    "drb014": ("Loop-carried", "Cross-row read (j-1 at j=0)"),
    "drb015": ("Loop-carried", "Cross-row read (var. length)"),
    "drb005": ("Loop-carried", "Indirect indexing"),
    "drb006": ("Loop-carried", "Indirect indexing"),
    "drb009": ("Shared cell", "Shared write"),
    "drb016": ("Shared cell", "Write-after-write"),
    "drb020": ("Shared cell", "Shared temporary"),
    "drb011": ("Shared cell", "Shared decrement"),
    "drb018": ("Shared cell", "Shared increment"),
    # Not used in the tuning of the proof guide.
    "drbheld033": ("Loop-carried", "Read-after-write (affine index)"),
    "drbheld037": ("Loop-carried", "Read-after-write (in seq. loop)"),
    "drbheld179": ("Loop-carried", "Write-after-write (conditional)"),
    "drbheld204": ("Loop-carried", "Affine read (2i vs. i+64)"),
    "drbheld206": ("Loop-carried", "Affine write (2i vs. i+64)"),
    "drbheld207": ("Loop-carried", "Read-after-write (distance 64)"),
    "drbheld197": ("Loop-carried", "Overlapping buffers (fixed offset)"),
    "drbheld195": ("Loop-carried", "Stencil on aliased buffers"),
    "drbheld039": ("Shared cell", "Read of a[0] while iter. 0 writes"),
    "drbheld202": ("Shared cell", "Read of a[64] while iter. 64 writes"),
    "drbheld111": ("Shared cell", "Shared index counter"),
    "drbheld169": ("Shared cell", "Shared scratch array"),
    "drbheld124": ("Missing sync.", "Missing barrier after write"),
    "drbheld160": ("Missing sync.", "Missing barrier between loops"),
    "drbheld074": ("Missing sync.", "Read outside the lock"),
    "drbheld119": ("Missing sync.", "Increment outside the lock"),
    "drbheld201": ("Missing sync.", "Write after empty critical section"),
    "drbheld191": ("Missing sync.", "Distinct critical sections"),
    "drbheld193": ("Missing sync.", "Distinct critical sections (flag)"),
    "drbheld185": ("Missing sync.", "Broken custom barrier (flags)"),
    "drbheld187": ("Missing sync.", "Broken lock-based barrier (2 locks)"),
    "drbheld189": ("Missing sync.", "Broken lock-based barrier (3 locks)"),
}

# linNNN / linheldNNN code -> (family, qualitative bug description)
LIN_META = {
    "lin001": ("Stack", "Lost push (non-atomic store)"),
    "lin002": ("Stack", "Double pop (non-atomic store)"),
    "lin003": ("Stack", "Clobbering push (fresh-read CAS)"),
    "lin004": ("Stack", "Lost push (discarded CAS)"),
    "lin005": ("Stack", "Spurious empty pop (no retry)"),
    "lin006": ("Queue", "Lost dequeue (no retry)"),
    "lin007": ("Queue", "Double dequeue (blind store)"),
    "lin008": ("Queue", "Double dequeue (fresh-read CAS)"),
    "lin009": ("Queue", "Lost enqueue (discarded CAS)"),
    "lin010": ("Queue", "Double dequeue (stale peek)"),
    "lin011": ("Hash table", "Lost add (blind store, add)"),
    "lin012": ("Hash table", "Lost add (blind store, remove)"),
    "lin013": ("Hash table", "Lost add (fresh-read CAS)"),
    "lin014": ("Hash table", "Lost add (CAS-fail reports ok)"),
    "lin015": ("Hash table", "Double add (stale lookup)"),
    # Not used in the tuning of the proof guide.
    "linheld016": ("2-lock queue", "Lost enqueue (no lock)"),
    "linheld017": ("2-lock queue", "Double dequeue (unlocked read)"),
    "linheld018": ("2-lock queue", "Spurious empty dequeue (late link)"),
    "linheld019": ("2-lock queue", "Double dequeue (split section)"),
    "linheld020": ("Harris list", "Lost add (no logical deletion)"),
    "linheld021": ("Harris list", "Removed key visible (mark ignored)"),
    "linheld022": ("Harris list", "Double remove (unchecked mark)"),
    "linheld023": ("Harris list", "Lost add (retry on deleted node)"),
}


def lin_family(code):
    """Family of a linNNN / linheldNNN case (e.g. 'Stack'), or None if not a listed case."""
    entry = LIN_META.get(code)
    return entry[0] if entry else None
