From iris.proofmode Require Import base proofmode.

From mizzle.lang Require Export semantics.

From mizzle.logic Require Import interp goal goal_proof goal_tactics adequacy.
From mizzle.stdlib Require Import rand.
From mizzle.pure_logic Require Import linear.

(** [emit] records on the global ghost trace; the adequacy theorem supplies
    the initial empty-trace fragment. *)

(** Events [bool * value]: bool tags [Call] (true) / [Ret] (false). *)
Definition mkCall : val := vfun: "v" => (true, "v").
Definition mkRet : val := vfun: "v" => (false, "v").

(** Record the pair [(i, v)] on the ghost trace. *)
Definition emit : val :=
  vfun: "i" "v" => Emit ("i", "v").

(** MizzleLang realisation of [linear.adv_step]'s adversarial client: [init ()],
    then fork [nondet_bool]-many concurrent [op obj (gen ())]. *)
Definition most_general_client : val :=
  vfun: "init" "op" "gen" =>
  let: "obj" := "init" () in
  let: "onecall" :=
    fun: "i" =>
      let: "x" := "gen" () in
      emit "i" (mkCall "x");;
      let: "r" := "op" "obj" "x" in
      emit "i" (mkRet "r") in
  let: "client" :=
    rec: "self" "i" =>
    if: nondet_bool () then ()
    else (
      Fork ("onecall" "i") ;;
      "self" ("i" + #1)
    ) in
    "client" #1.

(** [onecall] with [op]/[obj]/[gen] substituted — the form each forked
    thread runs (named so the [goal_onecall_*] wrappers can mention it). *)
Definition onecall_clo (op obj gen : val) : val :=
  (vfun: "i" =>
     let: "x" := gen () in
     emit "i" (mkCall "x") ;;
     let: "r" := op obj "x" in
     emit "i" (mkRet "r"))%V.

(** Decode an observation [(i, (b, x))] to a [linear] event (index [i] =
    tag); [decode_trace] lifts it to the checker's trace. *)

Definition decode_event (o : observation) : option (positive * trace) :=
  match o with
  | ValTuple [ValInt i; ValTuple [ValBool true;  x]] => Some (Z.to_pos i, Call x)
  | ValTuple [ValInt i; ValTuple [ValBool false; x]] => Some (Z.to_pos i, Ret  x)
  | _ => None
  end.

Definition decode_trace (tr : list observation) : list (positive * trace) :=
  omap decode_event tr.

Section client.
Context `{seqlogGS Σ}.

(** [Trace ks]: the observations decode to [ks] (backed by
    [trace_model]). *)
Definition Trace (ks : list (positive * trace)) : iProp Σ :=
  (∃ tr, trace_model tr ∗ ⌜decode_trace tr = ks⌝)%I.

(** The empty trace. *)
Lemma Trace_intro : trace_model [] -∗ Trace [].
Proof. iIntros "Hpm". iExists []. by iFrame. Qed.

(** Read-off: [ts] is the trace [tr], decoded. *)
Lemma Trace_read ts es σ tr :
  interp es σ tr -∗ Trace ts -∗ ⌜decode_trace tr = ts⌝.
Proof.
  iIntros "Hi (%tr' & Hpm & %Heq)".
  iDestruct (interp_trace with "Hi Hpm") as %->. done.
Qed.

(** Append a [Call x] event for op [i]. *)
Lemma Trace_emit_call E pp ks (i:Z) (x:val) ts :
  running pp (fill ks (Emit (Val (ValTuple [ValInt i; ValTuple [ValBool true; x]])))) -∗
  Trace ts -∗
  (running pp (fill ks Unit) -∗ Trace (ts ++ [(Z.to_pos i, Call x)]) -∗ goal E) -∗
  goal E.
Proof.
  iIntros "Hrun (%tr & Htr & %Heq) Hcont".
  iApply (goal_emit E pp ks _ tr with "Hrun Htr").
  iIntros "Hrun Htr".
  iApply ("Hcont" with "Hrun").
  iExists _. iFrame "Htr". iPureIntro.
  rewrite /decode_trace omap_app /=. by rewrite -Heq.
Qed.

(** Append a [Ret x] event for op [i]. *)
Lemma Trace_emit_ret E pp ks (i:Z) (x:val) ts :
  running pp (fill ks (Emit (Val (ValTuple [ValInt i; ValTuple [ValBool false; x]])))) -∗
  Trace ts -∗
  (running pp (fill ks Unit) -∗ Trace (ts ++ [(Z.to_pos i, Ret x)]) -∗ goal E) -∗
  goal E.
Proof.
  iIntros "Hrun (%tr & Htr & %Heq) Hcont".
  iApply (goal_emit E pp ks _ tr with "Hrun Htr").
  iIntros "Hrun Htr".
  iApply ("Hcont" with "Hrun").
  iExists _. iFrame "Htr". iPureIntro.
  rewrite /decode_trace omap_app /=. by rewrite -Heq.
Qed.

(** Drive [emit i (mkCall/mkRet x)] to one trace step. *)
Lemma goal_emit_call E pp ks (i:Z) (x:val) ts :
  running pp (fill ks (emit (Val (ValInt i)) (mkCall (Val x)))) -∗
  Trace ts -∗
  (running pp (fill ks Unit) -∗ Trace (ts ++ [(Z.to_pos i, Call x)]) -∗ goal E) -∗
  goal E.
Proof.
  iIntros "Hp Htr Hcont".
  rewrite /emit /mkCall.
  g_focus (App (Val _) (Val _)) "Hp".
  g_call "Hp". g_block "Hp". g_call2 "Hp". g_block "Hp".
  iApply (Trace_emit_call with "Hp Htr"). iIntros "Hp Htr".
  iApply ("Hcont" with "Hp Htr").
Qed.

Lemma goal_emit_ret E pp ks (i:Z) (x:val) ts :
  running pp (fill ks (emit (Val (ValInt i)) (mkRet (Val x)))) -∗
  Trace ts -∗
  (running pp (fill ks Unit) -∗ Trace (ts ++ [(Z.to_pos i, Ret x)]) -∗ goal E) -∗
  goal E.
Proof.
  iIntros "Hp Htr Hcont".
  rewrite /emit /mkRet.
  g_focus (App (Val _) (Val _)) "Hp".
  g_call "Hp". g_block "Hp". g_call2 "Hp". g_block "Hp".
  iApply (Trace_emit_ret with "Hp Htr"). iIntros "Hp Htr".
  iApply ("Hcont" with "Hp Htr").
Qed.

(** [onecall] wrappers: [_call] runs [gen] (via [Hgen]) + the [Call] emit,
    leaving the thread on [op obj v]; [_ret] runs the [Ret] emit. So an op
    is [call ; <op driver> ; ret], the driver free to park/resume. [[card]] *)
Lemma goal_onecall_call E (op obj gen : val) pk ks (i : Z) (v : val) ts :
  (∀ E' pp ks', running pp (fill ks' (gen (Val ValUnit))) -∗
                (running pp (fill ks' (Val v)) -∗ goal E') -∗ goal E') →
  running pk (fill ks (onecall_clo op obj gen (Val (ValInt i)))) -∗
  Trace ts -∗
  (running pk (fill (CtxLet "r" (emit #i (mkRet "r")) :: ks)
                    (App (App (Val op) (Val obj)) (Val v))) -∗
   Trace (ts ++ [(Z.to_pos i, Call v)]) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hgen) "Hp Htr Hcont".
  rewrite /onecall_clo. g_call "Hp".
  iApply (Hgen E pk (CtxLet "x" _ :: ks) with "Hp"). iIntros "Hp".
  iSimpl in "Hp". g_let "Hp".
  iApply (goal_emit_call E pk (CtxLet BAnon _ :: ks) i v ts with "Hp Htr").
  iIntros "Hp Htr".
  iSimpl in "Hp". g_let "Hp".
  iApply ("Hcont" with "Hp Htr").
Qed.

(** The [Ret] half of [onecall]: from the bare return value [r] under the
    [let: "r"] context left by [goal_onecall_call]. [[card]] *)
Lemma goal_onecall_ret E pk ks (i : Z) (r : val) ts :
  running pk (fill (CtxLet "r" (emit #i (mkRet "r")) :: ks) (Val r)) -∗
  Trace ts -∗
  (running pk (fill ks Unit) -∗ Trace (ts ++ [(Z.to_pos i, Ret r)]) -∗ goal E) -∗
  goal E.
Proof.
  iIntros "Hp Htr Hcont".
  iSimpl in "Hp". g_let "Hp".
  iApply (goal_emit_ret E pk ks i r ts with "Hp Htr"). iIntros "Hp Htr".
  iApply ("Hcont" with "Hp Htr").
Qed.

(** Deposit a finished [Trace T] into the witness obligation. [[card]] *)
Lemma Trace_fulfill T :
  remaining (Trace T) -∗ Trace T -∗ goal ⊤.
Proof.
  iIntros "Hrem Htr".
  iApply (fulfill with "[Htr Hrem]"); last by iModIntro.
  iApply (update_remaining (Trace T) True with "[Htr] Hrem").
  iIntros "_". iExact "Htr".
Qed.

End client.
