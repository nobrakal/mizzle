type binder =
  Name.t option

type field =
  string

type tag =
  string

type rec_flag = Asttypes.rec_flag =
  | Nonrecursive
  | Recursive

(* Whether a memory access is atomic. Zoo's [Load]/[Store] erased this
   distinction; Mizzle's data-race predicate ([logic/race.v]) needs it, since a
   race requires a non-atomic participant. *)
type atomicity =
  | Atomic
  | Not_atomic

type mutability =
  | Mutable
  | Immutable_nongenerative
  | Immutable_generative_weak
  | Immutable_generative_strong

type typ =
  | Type_product of field list
  | Type_record of field list
  | Type_variant of tag list

type pattern =
  | Pat_var of Name.t
  | Pat_tuple of binder list
  | Pat_constr of tag * binder list

type unop =
  | Unop_neg
  | Unop_minus

type binop =
  | Binop_plus | Binop_minus | Binop_mult | Binop_quot | Binop_rem
  | Binop_land | Binop_lor | Binop_lsl | Binop_lsr
  | Binop_eq | Binop_ne | Binop_le | Binop_lt | Binop_ge | Binop_gt
  | Binop_and | Binop_or
  | Binop_structeq | Binop_structne

type expression =
  | Global of Spath.t
  | Local of Name.t
  | Bool of bool
  | Int of int
  | Let of pattern * expression * expression
  | Letrec of rec_flag * Name.t * binder list * expression * expression
  | Seq of expression * expression
  | Fun of binder list * expression
  | Apply of expression * expression list
  | Unop of unop * expression
  | Binop of binop * expression * expression
  | If of expression * expression * expression option
  | While of expression * expression
  | For of binder * expression * expression * expression
  | Alloc of expression * expression
  | Tuple of expression list
  | Ref of expression
  | Record of expression list
  | Constr of mutability * tag * expression list
  | Proj of expression * field
  | Match of expression * branch list * fallback option
  | Ref_get of atomicity * expression
  | Ref_set of atomicity * expression * expression
  | Record_get of expression * field
  | Record_set of expression * field * expression
  | Is_immediate of expression
  | Get_tag of expression
  | Get_size of expression
  | Atomic_loc of expression * field
  | Load of atomicity * expression * expression
  | Store of atomicity * expression * expression * expression
  | Xchg of expression * expression
  | Cas of expression * expression * expression
  | Faa of expression * expression
  | Fail
  | Skip
and branch =
  { branch_tag: tag
  ; branch_fields: binder list
  ; branch_as: binder
  ; branch_expr: expression
  }
and fallback =
  { fallback_as: binder
  ; fallback_expr: expression
  }

type value =
  | Val_expr of Name.t * expression
  | Val_fun of Name.t * binder list * expression
  | Val_recs of (Name.t * Name.t * binder list * expression) list
  | Val_opaque of Name.t

type definition =
  | Type of Name.t * typ
  | Val of value

type t =
  { library: string
  ; module_: string
  ; dependencies: (string, string Hashset.t) Hashtbl.t
  ; definitions: definition list
  }

let rec expression_is_value = function
  | Global _
  | Bool _
  | Int _
  | Fun _ ->
      true
  | Tuple exprs
  | Constr ((Immutable_nongenerative | Immutable_generative_weak), _, exprs) ->
      List.for_all expression_is_value exprs
  | Local _
  | Let _
  | Letrec _
  | Seq _
  | Apply _
  | Unop _
  | Binop _
  | If _
  | While _
  | For _
  | Alloc _
  | Ref _
  | Record _
  | Constr (_, _, _)
  | Proj _
  | Match _
  | Ref_get _
  | Ref_set _
  | Record_get _
  | Record_set _
  | Is_immediate _
  | Get_tag _
  | Get_size _
  | Atomic_loc _
  | Load _
  | Store _
  | Xchg _
  | Cas _
  | Faa _
  | Fail
  | Skip ->
      false

let types str =
  List.filter_map (function Type (global, ty) -> Some (global, ty) | _ -> None) str.definitions
let values str =
  List.filter_map (function Val val_ -> Some val_ | _ -> None) str.definitions
