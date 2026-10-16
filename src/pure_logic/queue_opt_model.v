(** * FIFO queue model with option responses ****************************

    Like [stack_model.v] but FIFO: [Enq x] appends to the back; [Deq]
    removes from the front (the list head). Responses are option-wrapped to
    match the wrapped [op] of the [cases] Michael-Scott queues
    ([linearizable/bin/lin0NN_ms_queue*.ml]):

      - [‘QEnq(x)] enqueues and yields [§None];
      - [§QDeq] dequeues: [‘Some(v)] (front) when non-empty, [§None] when empty.

    Self-contained. Request tags use index 0/1; since [in_type] ignores its
    string argument, these match the [Enq]/[Deq] tags emitted by [ocaml2mizzle]
    for the [cases] library. (Distinct from [queue_model.v], which uses bare
    responses and a blocking deq.) *)

From stdpp Require Import ssreflect.
From stdpp Require Import relations gmap list.

From mizzle.lang Require Import semantics.

From mizzle.pure_logic Require Import linear linear_check.

(** ** Tags ****************************************************************)

Notation "'QEnq'" :=
  (in_type "pure_logic.queue_opt.req" 0)
  (in custom mizzle_tag).
Notation "'QDeq'" :=
  (in_type "pure_logic.queue_opt.req" 1)
  (in custom mizzle_tag).

(** ** Model ***************************************************************

    State is the contents from front (head of list) to back. [QEnq]
    appends; [QDeq] removes the head (response [‘Some(v)]) and is a no-op
    returning [§None] on the empty queue. *)

Inductive queue_request_response :
  list val → val → list val → val → Prop :=
  | q_rr_enq s x :
      queue_request_response s ‘QEnq( x )%V (s ++ [x]) §None%V
  | q_rr_deq_some v s :
      queue_request_response (v :: s) §QDeq%V s ‘Some( v )%V
  | q_rr_deq_empty :
      queue_request_response [] §QDeq%V [] §None%V.

Definition queue_valid_request (v : val) : Prop :=
  v = §QDeq%V ∨ ∃ x, v = ‘QEnq( x )%V.

Global Instance queue_opt_model : model := {|
  S := list val;
  s_init := [];
  valid_request := queue_valid_request;
  request_response := queue_request_response;
|}.

(** ** Executable step function *******************************************)

Definition queue_step (s : list val) (req res : val) : option (list val) :=
  match req with
  | ValBlock Nongenerative tag [x] =>
      if bool_decide (tag = in_type "pure_logic.queue_opt.req" 0) then
        match res with
        | ValBlock Nongenerative rtag [] =>
            if bool_decide (rtag = in_type "option" 0) then Some (s ++ [x]) else None
        | _ => None
        end
      else None
  | ValBlock Nongenerative tag [] =>
      if bool_decide (tag = in_type "pure_logic.queue_opt.req" 1) then
        match res with
        | ValBlock Nongenerative rtag [v] =>
            if bool_decide (rtag = in_type "option" 1) then
              match s with
              | v' :: s' => if bool_decide (v' = v) then Some s' else None
              | [] => None
              end
            else None
        | ValBlock Nongenerative rtag [] =>
            if bool_decide (rtag = in_type "option" 0) then
              match s with
              | [] => Some []
              | _ :: _ => None
              end
            else None
        | _ => None
        end
      else None
  | _ => None
  end.

Global Instance queue_opt_executable_model : executable_model :=
  {| step := queue_step |}.

(** ** Soundness/completeness *********************************************)

Lemma queue_step_sound s req res s' :
  queue_step s req res = Some s' →
  queue_valid_request req ∧ queue_request_response s req s' res.
Proof.
  unfold queue_step.
  destruct req as [|? ?|gen tag vs]; try discriminate.
  destruct gen; try discriminate.
  destruct vs as [|x [|? ?]]; try discriminate.
  - (* 0-arg block: §QDeq *)
    case_bool_decide as Htag; last discriminate.
    destruct res as [|? ?|rgen rtag rvs]; try discriminate.
    destruct rgen; try discriminate.
    destruct rvs as [|v [|? ?]]; try discriminate.
    + (* res 0-arg: §None → empty-queue deq *)
      case_bool_decide as Hrtag; last discriminate.
      destruct s as [|? ?]; last discriminate.
      intros [= <-]. subst tag rtag. split.
      * by left.
      * constructor.
    + (* res 1-arg: ‘Some(v) → deq front *)
      case_bool_decide as Hrtag; last discriminate.
      destruct s as [|v' s0]; first discriminate.
      case_bool_decide as Hv; last discriminate.
      intros [= <-]. subst tag rtag v'. split.
      * by left.
      * constructor.
  - (* 1-arg block: ‘QEnq(x) *)
    case_bool_decide as Htag; last discriminate.
    destruct res as [|? ?|rgen rtag rvs]; try discriminate.
    destruct rgen; try discriminate.
    destruct rvs as [|? ?]; try discriminate.
    case_bool_decide as Hrtag; last discriminate.
    intros [= <-]. subst tag rtag. split.
    * right. by exists x.
    * constructor.
Qed.

Lemma queue_step_complete s req res s' :
  queue_valid_request req →
  queue_request_response s req s' res →
  queue_step s req res = Some s'.
Proof.
  intros _ Hrr. unfold queue_step.
  destruct Hrr as [s x | v s | ]; cbn.
  all: by repeat case_bool_decide.
Qed.

Global Instance queue_opt_executable_model_correct : executable_model_correct :=
  {| step_sound := queue_step_sound;
     step_complete := queue_step_complete |}.
