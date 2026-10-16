(** * LIFO stack model for the linearizability framework *****************

    Generic [model] + [executable_model] for a Treiber-style LIFO stack
    exposing a single [op req] entry point that dispatches on [‘SPush(x)]
    and [§SPop] requests. State is the contents from top (most recently
    pushed) to bottom; no capacity bound.

    Responses follow the wrapped [op] in [linearizable/bin/
    lin001_treiber_stack1.ml]:
      - [‘SPush(x)] pushes [x] and yields [§None] (push has no value);
      - [§SPop] pops the top: [‘Some(v)] when non-empty (removing it),
        or [§None] when the stack is empty (state unchanged).

    Self-contained — does not depend on any MizzleLang program. The request tags
    use index 0/1; since [in_type] ignores its string argument (it is just
    documentation, [in_type _ n := n]), these match the [Push]/[Pop] tags
    emitted by [ocaml2mizzle] for the [cases] library regardless of the string.
    Mirrors [pure_logic/queue_model.v]. *)

From stdpp Require Import ssreflect.
From stdpp Require Import relations gmap list.

From mizzle.lang Require Import semantics.

From mizzle.pure_logic Require Import linear linear_check.

(** ** Tags ****************************************************************)

Notation "'SPush'" :=
  (in_type "pure_logic.stack.req" 0)
  (in custom mizzle_tag).
Notation "'SPop'" :=
  (in_type "pure_logic.stack.req" 1)
  (in custom mizzle_tag).

(** ** Model ***************************************************************

    Top of stack is the head of the list. [SPush] prepends; [SPop] removes
    the head when present (response [‘Some(v)]) and is a no-op returning
    [§None] on the empty stack. *)

Inductive stack_request_response :
  list val → val → list val → val → Prop :=
  | stack_rr_push s x :
      stack_request_response s ‘SPush( x )%V (x :: s) §None%V
  | stack_rr_pop_some v s :
      stack_request_response (v :: s) §SPop%V s ‘Some( v )%V
  | stack_rr_pop_empty :
      stack_request_response [] §SPop%V [] §None%V.

Definition stack_valid_request (v : val) : Prop :=
  v = §SPop%V ∨ ∃ x, v = ‘SPush( x )%V.

Global Instance stack_model : model := {|
  S := list val;
  s_init := [];
  valid_request := stack_valid_request;
  request_response := stack_request_response;
|}.

(** ** Executable step function *******************************************

    Pure pattern match on the [ValBlock] shape of [req] (and [res]):
      - 1-arg block, [SPush] tag, [res = §None]: push.
      - 0-arg block, [SPop] tag:
          [res = ‘Some(v)] with [s = v :: s']: pop the top;
          [res = §None] with [s = []]: empty-stack pop. *)

Definition stack_step (s : list val) (req res : val) : option (list val) :=
  match req with
  | ValBlock Nongenerative tag [x] =>
      if bool_decide (tag = in_type "pure_logic.stack.req" 0) then
        match res with
        | ValBlock Nongenerative rtag [] =>
            if bool_decide (rtag = in_type "option" 0) then Some (x :: s) else None
        | _ => None
        end
      else None
  | ValBlock Nongenerative tag [] =>
      if bool_decide (tag = in_type "pure_logic.stack.req" 1) then
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

Global Instance stack_executable_model : executable_model :=
  {| step := stack_step |}.

(** ** Soundness/completeness *********************************************

    Roundtrip between [stack_step] and [stack_request_response]. *)

Lemma stack_step_sound s req res s' :
  stack_step s req res = Some s' →
  stack_valid_request req ∧ stack_request_response s req s' res.
Proof.
  unfold stack_step.
  destruct req as [|? ?|gen tag vs]; try discriminate.
  destruct gen; try discriminate.
  destruct vs as [|x [|? ?]]; try discriminate.
  - (* 0-arg block: §SPop *)
    case_bool_decide as Htag; last discriminate.
    destruct res as [|? ?|rgen rtag rvs]; try discriminate.
    destruct rgen; try discriminate.
    destruct rvs as [|v [|? ?]]; try discriminate.
    + (* res 0-arg: §None → empty-stack pop *)
      case_bool_decide as Hrtag; last discriminate.
      destruct s as [|? ?]; last discriminate.
      intros [= <-]. subst tag rtag. split.
      * by left.
      * constructor.
    + (* res 1-arg: ‘Some(v) → pop top *)
      case_bool_decide as Hrtag; last discriminate.
      destruct s as [|v' s0]; first discriminate.
      case_bool_decide as Hv; last discriminate.
      intros [= <-]. subst tag rtag v'. split.
      * by left.
      * constructor.
  - (* 1-arg block: ‘SPush(x) *)
    case_bool_decide as Htag; last discriminate.
    destruct res as [|? ?|rgen rtag rvs]; try discriminate.
    destruct rgen; try discriminate.
    destruct rvs as [|? ?]; try discriminate.
    case_bool_decide as Hrtag; last discriminate.
    intros [= <-]. subst tag rtag. split.
    * right. by exists x.
    * constructor.
Qed.

Lemma stack_step_complete s req res s' :
  stack_valid_request req →
  stack_request_response s req s' res →
  stack_step s req res = Some s'.
Proof.
  intros _ Hrr. unfold stack_step.
  (* Push / pop-non-empty / pop-empty: [cbn] exposes the (reflexive) tag and
     response [bool_decide]s, each discharged by [case_bool_decide]. *)
  destruct Hrr as [s x | v s | ]; cbn.
  all: by repeat case_bool_decide.
Qed.

Global Instance stack_executable_model_correct : executable_model_correct :=
  {| step_sound := stack_step_sound;
     step_complete := stack_step_complete |}.
