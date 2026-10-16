(** * FIFO queue model for the linearizability framework *****************

    Generic [model] + [executable_model] for a FIFO queue exposing a
    single [op req] entry point that dispatches on [‘QEnq(x)] and
    [§QDeq] requests. State is the contents from front (oldest) to back
    (newest); no capacity bound (boundary conditions in real
    implementations manifest to the model as non-returning operations,
    which produce no [Lin] event).

    Self-contained — does not depend on any MizzleLang program test. A queue's
    [op] dispatcher plugs in here. *)

From stdpp Require Import ssreflect.
From stdpp Require Import relations gmap list.

From mizzle.lang Require Import semantics.

From mizzle.pure_logic Require Import linear linear_check.

(** ** Tags ****************************************************************

    Use a generic tag string. *)

Notation "'QEnq'" :=
  (in_type "pure_logic.queue.req" 0)
  (in custom mizzle_tag).
Notation "'QDeq'" :=
  (in_type "pure_logic.queue.req" 1)
  (in custom mizzle_tag).

(** ** Model ***************************************************************)

Inductive queue_request_response :
  list val → val → list val → val → Prop :=
  | queue_rr_enq s x :
      queue_request_response s ‘QEnq( x )%V (s ++ [x]) ()%V
  | queue_rr_deq s v :
      queue_request_response (v :: s) §QDeq%V s v.

Definition queue_valid_request (v : val) : Prop :=
  v = §QDeq%V ∨ ∃ x, v = ‘QEnq( x )%V.

Global Instance queue_model : model := {|
  S := list val;
  s_init := [];
  valid_request := queue_valid_request;
  request_response := queue_request_response;
|}.

(** ** Executable step function *******************************************

    Pure pattern match on the [ValBlock] shape:
      - 1-arg block, [QEnq] tag, [res = ()]: enqueue.
      - 0-arg block, [QDeq] tag, queue non-empty, [res = front]: dequeue. *)

Definition queue_step (s : list val) (req res : val) : option (list val) :=
  match req with
  | ValBlock Nongenerative tag [x] =>
      if bool_decide (tag = in_type "pure_logic.queue.req" 0) then
        match res with ValUnit => Some (s ++ [x]) | _ => None end
      else None
  | ValBlock Nongenerative tag [] =>
      if bool_decide (tag = in_type "pure_logic.queue.req" 1) then
        match s with
        | v :: s' => if bool_decide (v = res) then Some s' else None
        | [] => None
        end
      else None
  | _ => None
  end.

Global Instance queue_executable_model : executable_model :=
  {| step := queue_step |}.

(** ** Soundness/completeness *********************************************

    Roundtrip between [queue_step] and [queue_request_response]. The
    proofs are mechanical (case analysis on [req] / on the inductive
    [queue_request_response]). *)

Lemma queue_step_sound s req res s' :
  queue_step s req res = Some s' →
  queue_valid_request req ∧ queue_request_response s req s' res.
Proof.
  unfold queue_step.
  destruct req as [|? ?|gen tag vs]; try discriminate.
  destruct gen; try discriminate.
  destruct vs as [|x [|? ?]]; try discriminate.
  - (* 0-arg block: §QDeq case *)
    case_bool_decide as Htag; last discriminate.
    destruct s as [|v s_rest]; first discriminate.
    case_bool_decide as Hres; last discriminate.
    intros [= <-]. subst tag res. split.
    + by left.
    + by constructor.
  - (* 1-arg block: ‘QEnq case. ValUnit = ValBlock Nongenerative 0 []
       — destruct [res] enough to expose this shape or contradict. *)
    case_bool_decide as Htag; last discriminate.
    destruct res as [|? ?|gen' tag' vs']; try discriminate.
    destruct gen'; try discriminate.
    destruct tag' as [|?]; try discriminate.
    destruct vs'; try discriminate.
    intros [= <-]. subst tag. split.
    + right. by exists x.
    + by constructor.
Qed.

Lemma queue_step_complete s req res s' :
  queue_valid_request req →
  queue_request_response s req s' res →
  queue_step s req res = Some s'.
Proof.
  intros _ Hrr. unfold queue_step.
  destruct Hrr as [s x | s v]; cbn.
  - (* Enq: req = ‘QEnq(x), res = (), s' = s ++ [x]. *)
    by rewrite (bool_decide_eq_true_2 _ eq_refl).
  - (* Deq: req = §QDeq, s = v :: rest, res = v, s' = rest. *)
    by rewrite (bool_decide_eq_true_2 _ eq_refl) (bool_decide_eq_true_2 _ eq_refl).
Qed.

Global Instance queue_executable_model_correct : executable_model_correct :=
  {| step_sound := queue_step_sound;
     step_complete := queue_step_complete |}.
