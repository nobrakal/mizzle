(* A two-lock FIFO queue (Michael and Scott, PODC 1996), exposed through a
   single [op] entry point dispatching [Enq]/[Deq], for the linearizability
   framework. The sequential model is pure_logic/queue_opt_model.v. *)

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
  let last = Atomic.get t.tail in
  Atomic.set last (Next (value, cell));
  Atomic.set t.tail cell

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
