(* The two-lock FIFO queue of Michael and Scott ("Simple, Fast, and Practical
   Non-Blocking and Blocking Concurrent Queue Algorithms", PODC 1996, Fig. 2),
   exposed through a single [op] entry point dispatching [Enq]/[Deq].

   The queue is a linked list of cells, [head] pointing to the cell holding
   the front node and [tail] to the open ([Nil]) cell at the back, as in the
   Michael-Scott queue variants. Enqueues serialize on [tail_lock] and
   dequeues on [head_lock], so one enqueue and one dequeue may run at once.
   When the queue is empty they touch the same cell, which is why the cells
   and the [head]/[tail] pointers are atomic even though every write happens
   under a lock.

   Written in the ocaml2mizzle-translatable subset of OCaml, like the [cases]
   variants derived from it ([linheld016]-[linheld019]). *)

type 'a node = Nil | Next of 'a * 'a node Atomic.t

type 'a t = {
  head : 'a node Atomic.t Atomic.t;
  tail : 'a node Atomic.t Atomic.t;
  head_lock : Mutex.t;
  tail_lock : Mutex.t;
}

type 'a req =
  | Enq of 'a
  | Deq

let create () =
  let cell = Atomic.make Nil in
  {
    head = Atomic.make cell;
    tail = Atomic.make cell;
    head_lock = Mutex.create ();
    tail_lock = Mutex.create ();
  }

let push t value =
  let cell = Atomic.make Nil in
  Mutex.lock t.tail_lock;
  let last = Atomic.get t.tail in
  Atomic.set last (Next (value, cell));
  Atomic.set t.tail cell;
  Mutex.unlock t.tail_lock

let pop t =
  Mutex.lock t.head_lock;
  let first = Atomic.get t.head in
  match Atomic.get first with
  | Nil ->
      Mutex.unlock t.head_lock;
      None
  | Next (value, next) ->
      Atomic.set t.head next;
      Mutex.unlock t.head_lock;
      Some value

let op t req =
  match req with
  | Enq x -> push t x; None
  | Deq -> pop t
