From iris.proofmode Require Import base proofmode.

From mizzle.lang Require Export semantics.
From mizzle.lang Require Import instances.

From mizzle.logic Require Import interp goal.

Section race.
Context `{seqlogGS Σ}.

(** How an expression touches an address: whether it writes, and whether it
    does so atomically.  Both matter for a data race, which needs a write
    *and* a non-atomic participant — two atomic accesses to one address do
    not race, which is the whole point of atomics. *)
Record access_kind := AccessKind
  { access_write : bool
  ; access_atomicity : atomicity
  }.

Notation ReadNA := (AccessKind false NotAtomic) (only parsing).
Notation WriteNA := (AccessKind true NotAtomic) (only parsing).

(** An access of expression [e] to absolute address [l +ₗ fld].
    The read-modify-writes [CAS] / [Xchg] / [FAA] are atomic by
    construction, so they carry [Atomic]; a plain field access carries
    whatever its own flag says. *)
Inductive local_access : expr -> location -> access_kind -> Prop :=
| access_get_field atm (l:location) (fld:Z) :
    local_access
      (GetField atm (Val (ValLoc l)) (Val (ValInt fld)))
      (l +ₗ fld) (AccessKind false atm)
| access_set_field atm (l:location) (fld:Z) (w:val) :
    local_access
      (SetField atm (Val (ValLoc l)) (Val (ValInt fld)) (Val w))
      (l +ₗ fld) (AccessKind true atm)
| access_cas (l:location) (fld:Z) (v1 v2:val) :
    local_access
      (CAS (Val (ValTuple [ValLoc l; ValInt fld])) (Val v1) (Val v2))
      (l +ₗ fld) (AccessKind true Atomic)
| access_xchg (l:location) (fld:Z) (w:val) :
    local_access
      (Xchg (Val (ValTuple [ValLoc l; ValInt fld])) (Val w))
      (l +ₗ fld) (AccessKind true Atomic)
| access_faa (l:location) (fld:Z) (i:Z) :
    local_access
      (FAA (Val (ValTuple [ValLoc l; ValInt fld])) (Val (ValInt i)))
      (l +ₗ fld) (AccessKind true Atomic).

Definition access e l k := exists ks e', e = fill ks e' /\ local_access e' l k.

(** Two accesses to one address race when at least one writes and at least
    one is non-atomic.  Dropping the second condition would report a race
    between two atomic accesses; dropping the first, between two reads. *)
Definition races (k1 k2 : access_kind) : Prop :=
  (k1.(access_write) = true \/ k2.(access_write) = true) /\
  (k1.(access_atomicity) = NotAtomic \/ k2.(access_atomicity) = NotAtomic).

Definition is_racy p1 p2 : iProp Σ :=
  ∀ es σ ts, interp es σ ts -∗
    ⌜p1 ≠ p2 /\
     ∃ e1 e2 l k1 k2,
       es !! p1 = Some e1 /\ es !! p2 = Some e2 /\
       access e1 l k1 /\ access e2 l k2 /\
       races k1 k2⌝.

Definition is_racy' : iProp Σ := ∃ p1 p2, is_racy p1 p2.

Lemma is_racy_intro p1 p2 e1 e2 l k1 k2 :
  access e1 l k1 ->
  access e2 l k2 ->
  races k1 k2 ->
  running p1 e1 -∗ running p2 e2 -∗ is_racy p1 p2.
Proof.
  iIntros (Ha1 Ha2 Hw) "H1 H2".
  iIntros (es σ ts) "Hi".
  iDestruct (interp_running_exploit with "H1 Hi") as %Hl1.
  iDestruct (interp_running_exploit with "H2 Hi") as %Hl2.
  iDestruct (ghost_map_elem_frac_ne with "H1 H2") as %Hne.
  { intros Hv. apply dfrac_valid_own_l in Hv.
    by apply Qp.lt_strict in Hv. }
  iPureIntro. split; first done.
  exists e1, e2, l, k1, k2. eauto 10.
Qed.

(** Closing pattern: once two threads are parked at conflicting accesses
    to the same address, the goal is fulfilled. [[card]] *)
Lemma goal_race_close p1 p2 e1 e2 l k1 k2 :
  access e1 l k1 ->
  access e2 l k2 ->
  races k1 k2 ->
  remaining is_racy' -∗ running p1 e1 -∗ running p2 e2 -∗ goal ⊤.
Proof.
  iIntros (Ha1 Ha2 Hk) "Hrem Hp1 Hp2".
  iApply (fulfill with "[Hp1 Hp2 Hrem]"); last by iModIntro.
  iApply (update_remaining with "[Hp1 Hp2] Hrem").
  iIntros "_". iExists p1, p2.
  iApply (is_racy_intro with "Hp1 Hp2"); eauto.
Qed.

End race.

(** Discharge a [races k1 k2] obligation once [solve_access] has pinned both
    access kinds to concrete constructors. *)
Ltac solve_races := split; auto.

(** Discharge an [access e l b] obligation by searching the evaluation
    spine of [e] for an access redex ([reshape_expr] backtracks past
    non-access nodes via the [econstructor] filter). Instantiates [l] and
    the access kind when they are evars, so [goal_race_close] can be applied without
    spelling out the racy address:
    [iApply (goal_race_close q0 q1 with "Hrem Hq0 Hq1"); [solve_access..| auto].]
    If an expression held several access redexes on its spine (it never
    does for a parked thread), the first one found wins. *)
Ltac solve_access :=
  lazymatch goal with
  | |- access (fill ?ks ?e) _ _ =>
      reshape_expr e ltac:(fun K e' =>
        exists (K ++ ks), e'; split; [by rewrite fill_app /= | econstructor])
  | |- access ?e _ _ =>
      reshape_expr e ltac:(fun K e' =>
        exists K, e'; split; [reflexivity | econstructor])
  end.

From mizzle.logic Require Import adequacy.

Section adequacy.

Definition racy '((es,σ) : (list expr * state)) :=
  ∃ p1 p2 e1 e2 l k1 k2,
    p1 ≠ p2 /\
    es !! p1 = Some e1 /\ es !! p2 = Some e2 /\
    access e1 l k1 /\ access e2 l k2 /\
    races k1 k2.

Lemma deduce_racy `{!seqlogGS Σ} es σ ts :
  interp es σ ts -∗ is_racy' -∗ ⌜racy (es, σ)⌝.
Proof.
  iIntros "Hi (%p1 & %p2 & Hr)".
  iDestruct ("Hr" with "Hi") as
    %(Hne & e1 & e2 & l & k1 & k2 & Hl1 & Hl2 & Ha1 & Ha2 & Hk).
  iPureIntro. exists p1, p2, e1, e2, l, k1, k2. eauto 10.
Qed.

(** Wire a goal-style driving lemma [remaining is_racy' -∗ focused p ks e
    -∗ goal ⊤] straight into adequacy: the whole top-level racy theorem of
    a case file is [apply goal_race_adequacy; intros; apply <driving>]. *)
Lemma goal_race_adequacy e v0 :
  (∀ `{!seqlogGS Σ} (p:nat) (ks:list ectxi),
     ⊢ remaining is_racy' -∗ running p (fill ks e) -∗ goal ⊤) ->
  exists c, rtc silent_step ([e], initial_state v0) c /\ racy c.
Proof.
  intros Hgoal.
  destruct (goal_adequacy (fun _ _ => is_racy') e v0 racy)
    as (c&Hrtc&Hrc).
  { iIntros (??) "(Hrem & Hrun & _)".
    iSplitL.
    { iApply (Hgoal _ _ 0 [] with "Hrem Hrun"). }
    { iIntros (???) "(?&X)". iApply (deduce_racy with "[$][$]"). } }
  eauto.
Qed.

End adequacy.
