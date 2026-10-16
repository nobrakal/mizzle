(** * Finite-map model with boolean responses *************************

    Sequential spec for the [cases] hash tables
    ([linearizable/bin/lin0NN_htbl*.ml]). State is an association list of
    key/value pairs with unique keys (front = most recently inserted). The
    wrapped [op] dispatches on three request tags, each returning a [bool]:

      - [‘HAdd(k,v)] inserts [(k,v)] if [k] is absent, yielding [true];
        if [k] is already present it changes nothing, yielding [false];
      - [‘HRemove(k)] deletes [k] if present, yielding [true]; otherwise
        changes nothing, yielding [false];
      - [‘HMem(k)] yields [true] iff [k] is present (state unchanged).

    Self-contained. Request tags use index 0/1/2; since [in_type] ignores
    its string argument, these match the [Add]/[Remove]/[Mem] tags emitted
    by [ocaml2mizzle] for the [cases] library. *)

From stdpp Require Import ssreflect.
From stdpp Require Import relations gmap list.

From mizzle.lang Require Import semantics.

From mizzle.pure_logic Require Import linear linear_check.

(** ** Tags ****************************************************************)

Notation "'HAdd'" :=
  (in_type "pure_logic.htbl.req" 0)
  (in custom mizzle_tag).
Notation "'HRemove'" :=
  (in_type "pure_logic.htbl.req" 1)
  (in custom mizzle_tag).
Notation "'HMem'" :=
  (in_type "pure_logic.htbl.req" 2)
  (in custom mizzle_tag).

(** ** State helpers ******************************************************)

Fixpoint has_key (k : val) (s : list (val * val)) : bool :=
  match s with
  | [] => false
  | (k', _) :: rest => bool_decide (k' = k) || has_key k rest
  end.

Fixpoint remove_key (k : val) (s : list (val * val)) : list (val * val) :=
  match s with
  | [] => []
  | (k', v') :: rest =>
      if bool_decide (k' = k) then remove_key k rest
      else (k', v') :: remove_key k rest
  end.

(** ** Model ***************************************************************)

Inductive htbl_request_response :
  list (val * val) → val → list (val * val) → val → Prop :=
  | h_rr_add_new k v s :
      has_key k s = false →
      htbl_request_response s ‘HAdd( k, v )%V ((k, v) :: s) (ValBool true)
  | h_rr_add_dup k v s :
      has_key k s = true →
      htbl_request_response s ‘HAdd( k, v )%V s (ValBool false)
  | h_rr_remove_present k s :
      has_key k s = true →
      htbl_request_response s ‘HRemove( k )%V (remove_key k s) (ValBool true)
  | h_rr_remove_absent k s :
      has_key k s = false →
      htbl_request_response s ‘HRemove( k )%V s (ValBool false)
  | h_rr_mem_present k s :
      has_key k s = true →
      htbl_request_response s ‘HMem( k )%V s (ValBool true)
  | h_rr_mem_absent k s :
      has_key k s = false →
      htbl_request_response s ‘HMem( k )%V s (ValBool false).

Definition htbl_valid_request (v : val) : Prop :=
  (∃ k x, v = ‘HAdd( k, x )%V) ∨ (∃ k, v = ‘HRemove( k )%V) ∨
  (∃ k, v = ‘HMem( k )%V).

Global Instance htbl_model : model := {|
  S := list (val * val);
  s_init := [];
  valid_request := htbl_valid_request;
  request_response := htbl_request_response;
|}.

(** ** Executable step function *******************************************)

Definition htbl_step (s : list (val * val)) (req res : val) :
  option (list (val * val)) :=
  match req with
  | ValBlock Nongenerative tag [k; v] =>
      if bool_decide (tag = in_type "pure_logic.htbl.req" 0) then
        match res with
        | ValBool b =>
            if has_key k s then (if b then None else Some s)
            else (if b then Some ((k, v) :: s) else None)
        | _ => None
        end
      else None
  | ValBlock Nongenerative tag [k] =>
      if bool_decide (tag = in_type "pure_logic.htbl.req" 1) then
        match res with
        | ValBool b =>
            if has_key k s then (if b then Some (remove_key k s) else None)
            else (if b then None else Some s)
        | _ => None
        end
      else if bool_decide (tag = in_type "pure_logic.htbl.req" 2) then
        match res with
        | ValBool b =>
            if has_key k s then (if b then Some s else None)
            else (if b then None else Some s)
        | _ => None
        end
      else None
  | _ => None
  end.

Global Instance htbl_executable_model : executable_model :=
  {| step := htbl_step |}.

(** ** Soundness/completeness *********************************************)

Lemma htbl_step_sound s req res s' :
  htbl_step s req res = Some s' →
  htbl_valid_request req ∧ htbl_request_response s req s' res.
Proof.
  unfold htbl_step.
  destruct req as [|? ?|gen tag vs]; try discriminate.
  destruct gen; try discriminate.
  destruct vs as [|k [|v [|? ?]]]; try discriminate.
  - (* 1-arg block: HRemove or HMem *)
    case_bool_decide as Htag1.
    + (* HRemove *)
      destruct res as [[b| | |] | |]; try discriminate.
      destruct (has_key k s) eqn:Hk; destruct b; intros [= <-]; subst tag; split.
      * right; left; by eexists.
      * by apply h_rr_remove_present.
      * right; left; by eexists.
      * by apply h_rr_remove_absent.
    + case_bool_decide as Htag2; last discriminate.
      (* HMem *)
      destruct res as [[b| | |] | |]; try discriminate.
      destruct (has_key k s) eqn:Hk; destruct b; intros [= <-]; subst tag; split.
      * right; right; by eexists.
      * by apply h_rr_mem_present.
      * right; right; by eexists.
      * by apply h_rr_mem_absent.
  - (* 2-arg block: HAdd *)
    case_bool_decide as Htag; last discriminate.
    destruct res as [[b| | |] | |]; try discriminate.
    destruct (has_key k s) eqn:Hk; destruct b; intros [= <-]; subst tag; split.
    * left; by do 2 eexists.
    * by apply h_rr_add_dup.
    * left; by do 2 eexists.
    * by apply h_rr_add_new.
Qed.

Lemma htbl_step_complete s req res s' :
  htbl_valid_request req →
  htbl_request_response s req s' res →
  htbl_step s req res = Some s'.
Proof.
  intros _ Hrr. unfold htbl_step.
  destruct Hrr as [k v s Hk | k v s Hk | k s Hk | k s Hk | k s Hk | k s Hk]; cbn.
  all: rewrite ?Hk; by repeat case_bool_decide.
Qed.

Global Instance htbl_executable_model_correct : executable_model_correct :=
  {| step_sound := htbl_step_sound;
     step_complete := htbl_step_complete |}.
