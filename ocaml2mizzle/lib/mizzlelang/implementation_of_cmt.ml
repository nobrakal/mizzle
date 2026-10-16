open Implementation

module Dependency = struct
  let structeq =
    "zoo", "structural_equality"
  let diverge =
    "zoo_std", "diverge"
  let assert_ =
    "zoo_std", "assert"
  let assume =
    "zoo_std", "assume"
  (* The split-argument read-modify-writes. Spelled as a zoo_std module; the
     library mapping in mizzle.ml sends it to mizzle.stdlib/atomic_loc. *)
  let atomic_loc =
    "zoo_std", "atomic_loc"
end

module Builtin = struct
  let raising =
    [|[|"Stdlib";"raise"|] ;
      [|"Stdlib";"invalid_arg"|] ;
      [|"Stdlib";"failwith"|] ;
    |]
  let raising =
    Array.fold_left (fun acc path ->
      Path.Set.add (Path.of_array path) acc
    ) Path.Set.empty raising

  let paths =
    [|[|"Stdlib";"ignore"|],
      Fun ([None], Tuple []),
      None
    ; [|"Stdlib";"not"|],
      Fun ([Some "1"], Unop (Unop_neg, Local "1")),
      None
    ; [|"Stdlib";"~-"|],
      Fun ([Some "1"], Unop (Unop_minus, Local "1")),
      None
    ; [|"Stdlib";"+"|],
      Fun ([Some "1"; Some "2"], Binop (Binop_plus, Local "1", Local "2")),
      None
    ; [|"Stdlib";"-"|],
      Fun ([Some "1"; Some "2"], Binop (Binop_minus, Local "1", Local "2")),
      None
    ; [|"Stdlib";"*"|],
      Fun ([Some "1"; Some "2"], Binop (Binop_mult, Local "1", Local "2")),
      None
    ; [|"Stdlib";"/"|],
      Fun ([Some "1"; Some "2"], Binop (Binop_quot, Local "1", Local "2")),
      None
    ; [|"Stdlib";"mod"|],
      Fun ([Some "1"; Some "2"], Binop (Binop_rem, Local "1", Local "2")),
      None
    ; [|"Stdlib";"land"|],
      Fun ([Some "1"; Some "2"], Binop (Binop_land, Local "1", Local "2")),
      None
    ; [|"Stdlib";"lor"|],
      Fun ([Some "1"; Some "2"], Binop (Binop_lor, Local "1", Local "2")),
      None
    ; [|"Stdlib";"lsl"|],
      Fun ([Some "1"; Some "2"], Binop (Binop_lsl, Local "1", Local "2")),
      None
    ; [|"Stdlib";"lsr"|],
      Fun ([Some "1"; Some "2"], Binop (Binop_lsr, Local "1", Local "2")),
      None
    ; [|"Stdlib";"=="|],
      Fun ([Some "1"; Some "2"], Binop (Binop_eq, Local "1", Local "2")),
      None
    ; [|"Stdlib";"!="|],
      Fun ([Some "1"; Some "2"], Binop (Binop_ne, Local "1", Local "2")),
      None
    ; [|"Stdlib";"<="|],
      Fun ([Some "1"; Some "2"], Binop (Binop_le, Local "1", Local "2")),
      None
    ; [|"Stdlib";"<"|],
      Fun ([Some "1"; Some "2"], Binop (Binop_lt, Local "1", Local "2")),
      None
    ; [|"Stdlib";">="|],
      Fun ([Some "1"; Some "2"], Binop (Binop_ge, Local "1", Local "2")),
      None
    ; [|"Stdlib";">"|],
      Fun ([Some "1"; Some "2"], Binop (Binop_gt, Local "1", Local "2")),
      None
    ; [|"Stdlib";"&&"|],
      Fun ([Some "1"; Some "2"], Binop (Binop_and, Local "1", Local "2")),
      None
    ; [|"Stdlib";"||"|],
      Fun ([Some "1"; Some "2"], Binop (Binop_or, Local "1", Local "2")),
      None
    ; [|"Stdlib";"="|],
      Fun ([Some "1"; Some "2"], Binop (Binop_structeq, Local "1", Local "2")),
      Some Dependency.structeq
    ; [|"Stdlib";"<>"|],
      Fun ([Some "1"; Some "2"], Binop (Binop_structne, Local "1", Local "2")),
      Some Dependency.structeq
    ; [|"Stdlib";"ref"|],
      Fun ([Some "1"], Ref (Local "1")),
      None
    ; [|"Stdlib";"!"|],
      Fun ([Some "1"], Ref_get (Not_atomic, Local "1")),
      None
    ; [|"Stdlib";":="|],
      Fun ([Some "1"; Some "2"], Ref_set (Not_atomic, Local "1", Local "2")),
      None
    ; [|"Stdlib";"Obj";"repr"|],
      Fun ([Some "1"], Local "1"),
      None
    ; [|"Stdlib";"Obj";"obj"|],
      Fun ([Some "1"], Local "1"),
      None
    ; [|"Stdlib";"Obj";"magic"|],
      Fun ([Some "1"], Local "1"),
      None
    ; [|"Stdlib";"Obj";"is_int"|],
      Fun ([Some "1"], Is_immediate (Local "1")),
      None
    ; [|"Stdlib";"Obj";"tag"|],
      Fun ([Some "1"], Get_tag (Local "1")),
      None
    ; [|"Stdlib";"Obj";"size"|],
      Fun ([Some "1"], Get_size (Local "1")),
      None
    ; [|"Stdlib";"Obj";"field"|],
      Fun ([Some "1"; Some "2"], Load (Not_atomic, Local "1", Local "2")),
      None
    ; [|"Stdlib";"Obj";"set_field"|],
      Fun ([Some "1"; Some "2"; Some "3"], Store (Not_atomic, Local "1", Local "2", Local "3")),
      None
    ; [|"Stdlib";"Obj";"new_block"|],
      Fun ([Some "1"; Some "2"], Alloc (Local "1", Local "2")),
      None
    ; [|"Stdlib";"Atomic";"Loc";"get"|],
      Fun ([Some "1"], Load (Atomic, Proj (Local "1", "0"), Proj (Local "1", "1"))),
      None
    ; [|"Stdlib";"Atomic";"Loc";"set"|],
      Fun ([Some "1"; Some "2"], Store (Atomic, Proj (Local "1", "0"), Proj (Local "1", "1"), Local "2")),
      None
    ; [|"Stdlib";"Atomic";"Loc";"exchange"|],
      Fun ([Some "1"; Some "2"], Xchg (Local "1", Local "2")),
      None
    ; [|"Stdlib";"Atomic";"Loc";"compare_and_set"|],
      Fun ([Some "1"; Some "2"; Some "3"], Cas (Local "1", Local "2", Local "3")),
      None
    ; [|"Stdlib";"Atomic";"Loc";"fetch_and_add"|],
      Fun ([Some "1"; Some "2"], Faa (Local "1", Local "2")),
      None
    ; [|"Stdlib";"Atomic";"Loc";"decr"|],
      Fun ([Some "1"], Seq (Faa (Local "1", Int (-1)), Tuple [])),
      None
    ; [|"Stdlib";"Atomic";"Loc";"incr"|],
      Fun ([Some "1"], Seq (Faa (Local "1", Int 1), Tuple [])),
      None
    ; [|"Stdlib";"Atomic";"make"|],
      Fun ([Some "1"], Ref (Local "1")),
      None
    ; [|"Stdlib";"Atomic";"get"|],
      Fun ([Some "1"], Ref_get (Atomic, Local "1")),
      None
    ; [|"Stdlib";"Atomic";"set"|],
      Fun ([Some "1"; Some "2"], Ref_set (Atomic, Local "1", Local "2")),
      None
    ; [|"Stdlib";"Atomic";"exchange"|],
      Fun ([Some "1"; Some "2"], Xchg (Atomic_loc (Local "1", "contents"), Local "2")),
      Some Dependency.atomic_loc
    ; [|"Stdlib";"Atomic";"compare_and_set"|],
      Fun ([Some "1"; Some "2"; Some "3"], Cas (Atomic_loc (Local "1", "contents"), Local "2", Local "3")),
      Some Dependency.atomic_loc
    ; [|"Stdlib";"Atomic";"fetch_and_add"|],
      Fun ([Some "1"; Some "2"], Faa (Atomic_loc (Local "1", "contents"), Local "2")),
      Some Dependency.atomic_loc
    ; [|"Stdlib";"Atomic";"decr"|],
      Fun ([Some "1"], Seq (Faa (Atomic_loc (Local "1", "contents"), Int (-1)), Tuple [])),
      Some Dependency.atomic_loc
    ; [|"Stdlib";"Atomic";"incr"|],
      Fun ([Some "1"], Seq (Faa (Atomic_loc (Local "1", "contents"), Int 1), Tuple [])),
      Some Dependency.atomic_loc
    |]
  let paths =
    Array.fold_left (fun acc (path, expr, dep) ->
      Path.Map.add (Path.of_array path) (expr, dep) acc
    ) Path.Map.empty paths
  let paths =
    Path.Set.fold (fun path acc ->
      let expr = Fun ([None], Apply (Global Spath.Builtin.diverge, [Tuple []])) in
      let dep = Some Dependency.diverge in
      Path.Map.add path (expr, dep) acc
    ) raising paths

  type app =
    | Opaque of expression
    | Transparent of (expression list -> expression option)
  let apps =
    [|[|"Stdlib";"ignore"|],
      (function [expr] -> Some (Seq (expr, Tuple [])) | _ -> None),
      None
    ; [|"Stdlib";"not"|],
      (function [expr] -> Some (Unop (Unop_neg, expr)) | _ -> None),
      None
    ; [|"Stdlib";"~-"|],
      (function [expr] -> Some (Unop (Unop_minus, expr)) | _ -> None),
      None
    ; [|"Stdlib";"+"|],
      (function [expr1; expr2] -> Some (Binop (Binop_plus, expr1, expr2)) | _ -> None),
      None
    ; [|"Stdlib";"-"|],
      (function [expr1; expr2] -> Some (Binop (Binop_minus, expr1, expr2)) | _ -> None),
      None
    ; [|"Stdlib";"*"|],
      (function [expr1; expr2] -> Some (Binop (Binop_mult, expr1, expr2)) | _ -> None),
      None
    ; [|"Stdlib";"/"|],
      (function [expr1; expr2] -> Some (Binop (Binop_quot, expr1, expr2)) | _ -> None),
      None
    ; [|"Stdlib";"mod"|],
      (function [expr1; expr2] -> Some (Binop (Binop_rem, expr1, expr2)) | _ -> None),
      None
    ; [|"Stdlib";"land"|],
      (function [expr1; expr2] -> Some (Binop (Binop_land, expr1, expr2)) | _ -> None),
      None
    ; [|"Stdlib";"lor"|],
      (function [expr1; expr2] -> Some (Binop (Binop_lor, expr1, expr2)) | _ -> None),
      None
    ; [|"Stdlib";"lsl"|],
      (function [expr1; expr2] -> Some (Binop (Binop_lsl, expr1, expr2)) | _ -> None),
      None
    ; [|"Stdlib";"lsr"|],
      (function [expr1; expr2] -> Some (Binop (Binop_lsr, expr1, expr2)) | _ -> None),
      None
    ; [|"Stdlib";"=="|],
      (function [expr1; expr2] -> Some (Binop (Binop_eq, expr1, expr2)) | _ -> None),
      None
    ; [|"Stdlib";"!="|],
      (function [expr1; expr2] -> Some (Binop (Binop_ne, expr1, expr2)) | _ -> None),
      None
    ; [|"Stdlib";"<="|],
      (function [expr1; expr2] -> Some (Binop (Binop_le, expr1, expr2)) | _ -> None),
      None
    ; [|"Stdlib";"<"|],
      (function [expr1; expr2] -> Some (Binop (Binop_lt, expr1, expr2)) | _ -> None),
      None
    ; [|"Stdlib";">="|],
      (function [expr1; expr2] -> Some (Binop (Binop_ge, expr1, expr2)) | _ -> None),
      None
    ; [|"Stdlib";">"|],
      (function [expr1; expr2] -> Some (Binop (Binop_gt, expr1, expr2)) | _ -> None),
      None
    ; [|"Stdlib";"&&"|],
      (function [expr1; expr2] -> Some (Binop (Binop_and, expr1, expr2)) | _ -> None),
      None
    ; [|"Stdlib";"||"|],
      (function [expr1; expr2] -> Some (Binop (Binop_or, expr1, expr2)) | _ -> None),
      None
    ; [|"Stdlib";"="|],
      (function [expr1; expr2] -> Some (Binop (Binop_structeq, expr1, expr2)) | _ -> None),
      Some Dependency.structeq
    ; [|"Stdlib";"<>"|],
      (function [expr1; expr2] -> Some (Binop (Binop_structne, expr1, expr2)) | _ -> None),
      Some Dependency.structeq
    ; [|"Stdlib";"ref"|],
      (function [expr] -> Some (Ref expr) | _ -> None),
      None
    ; [|"Stdlib";"!"|],
      (function [expr] -> Some (Ref_get (Not_atomic, expr)) | _ -> None),
      None
    ; [|"Stdlib";":="|],
      (function [expr1; expr2] -> Some (Ref_set (Not_atomic, expr1, expr2)) | _ -> None),
      None
    ; [|"Stdlib";"Obj";"repr"|],
      (function [expr] -> Some expr | _ -> None),
      None
    ; [|"Stdlib";"Obj";"obj"|],
      (function [expr] -> Some expr | _ -> None),
      None
    ; [|"Stdlib";"Obj";"magic"|],
      (function [expr] -> Some expr | _ -> None),
      None
    ; [|"Stdlib";"Obj";"is_int"|],
      (function [expr] -> Some (Is_immediate expr) | _ -> None),
      None
    ; [|"Stdlib";"Obj";"tag"|],
      (function [expr] -> Some (Get_tag expr) | _ -> None),
      None
    ; [|"Stdlib";"Obj";"size"|],
      (function [expr] -> Some (Get_size expr) | _ -> None),
      None
    ; [|"Stdlib";"Obj";"field"|],
      (function [expr1; expr2] -> Some (Load (Not_atomic, expr1, expr2)) | _ -> None),
      None
    ; [|"Stdlib";"Obj";"set_field"|],
      (function [expr1; expr2; expr3] -> Some (Store (Not_atomic, expr1, expr2, expr3)) | _ -> None),
      None
    ; [|"Stdlib";"Obj";"new_block"|],
      (function [expr1; expr2] -> Some (Alloc (expr1, expr2)) | _ -> None),
      None
    ; [|"Stdlib";"Atomic";"Loc";"get"|],
      (function [expr] -> Some (Load (Atomic, Proj (expr, "0"), Proj (expr, "1"))) | _ -> None),
      None
    ; [|"Stdlib";"Atomic";"Loc";"set"|],
      (function [expr1; expr2] -> Some (Store (Atomic, Proj (expr1, "0"), Proj (expr1, "1"), expr2)) | _ -> None),
      None
    ; [|"Stdlib";"Atomic";"Loc";"exchange"|],
      (function [expr1; expr2] -> Some (Xchg (expr1, expr2)) | _ -> None),
      None
    ; [|"Stdlib";"Atomic";"Loc";"compare_and_set"|],
      (function [expr1; expr2; expr3] -> Some (Cas (expr1, expr2, expr3)) | _ -> None),
      None
    ; [|"Stdlib";"Atomic";"Loc";"fetch_and_add"|],
      (function [expr1; expr2] -> Some (Faa (expr1, expr2)) | _ -> None),
      None
    ; [|"Stdlib";"Atomic";"Loc";"decr"|],
      (function [expr] -> Some (Seq (Faa (expr, Int (-1)), Tuple [])) | _ -> None),
      None
    ; [|"Stdlib";"Atomic";"Loc";"incr"|],
      (function [expr] -> Some (Seq (Faa (expr, Int 1), Tuple [])) | _ -> None),
      None
    ; [|"Stdlib";"Atomic";"make"|],
      (function [expr] -> Some (Ref expr) | _ -> None),
      None
    ; [|"Stdlib";"Atomic";"get"|],
      (function [expr] -> Some (Ref_get (Atomic, expr)) | _ -> None),
      None
    ; [|"Stdlib";"Atomic";"set"|],
      (function [expr1; expr2] -> Some (Ref_set (Atomic, expr1, expr2)) | _ -> None),
      None
    ; [|"Stdlib";"Atomic";"exchange"|],
      (function [expr1; expr2] -> Some (Xchg (Atomic_loc (expr1, "contents"), expr2)) | _ -> None),
      Some Dependency.atomic_loc
    ; [|"Stdlib";"Atomic";"compare_and_set"|],
      (function [expr1; expr2; expr3] -> Some (Cas (Atomic_loc (expr1, "contents"), expr2, expr3)) | _ -> None),
      Some Dependency.atomic_loc
    ; [|"Stdlib";"Atomic";"fetch_and_add"|],
      (function [expr1; expr2] -> Some (Faa (Atomic_loc (expr1, "contents"), expr2)) | _ -> None),
      Some Dependency.atomic_loc
    ; [|"Stdlib";"Atomic";"decr"|],
      (function [expr] -> Some (Seq (Faa (Atomic_loc (expr, "contents"), Int (-1)), Tuple [])) | _ -> None),
      Some Dependency.atomic_loc
    ; [|"Stdlib";"Atomic";"incr"|],
      (function [expr] -> Some (Seq (Faa (Atomic_loc (expr, "contents"), Int 1), Tuple [])) | _ -> None),
      Some Dependency.atomic_loc
    |]
  let apps =
    Array.fold_left (fun acc (path, mk_expr, dep) ->
      Path.Map.add (Path.of_array path) (Transparent mk_expr, dep) acc
    ) Path.Map.empty apps
  let apps =
    Path.Set.fold (fun path acc ->
      let expr = Apply (Global Spath.Builtin.diverge, [Tuple []]) in
      let dep = Some Dependency.diverge in
      Path.Map.add path (Opaque expr, dep) acc
    ) raising apps

  let constrs =
    [|[|"()"|], Tuple [] ;
      [|"true"|], Bool true ;
      [|"false"|], Bool false ;
    |]
  let constrs =
    Array.fold_left (fun acc (lid, expr) ->
      Longident.Map.add (Longident.of_array lid) expr acc
    ) Longident.Map.empty constrs
end

module Unsupported = struct
  type t =
    | Literal_non_integer
    | Pattern_alias
    | Pattern_constant
    | Pattern_variant
    | Pattern_record
    | Pattern_array
    | Pattern_or
    | Pattern_lazy
    | Pattern_guard
    | Pattern_constr
    | Pattern_nested
    | Pattern_invalid
    | Pattern_non_trivial
    | Handler_exception
    | Expr_let_rec_non_function
    | Expr_let_mutual
    | Expr_for_downward
    | Expr_open
    | Expr_array
    | Expr_try
    | Expr_variant
    | Expr_send
    | Expr_new
    | Expr_inst_var
    | Expr_set_inst_var
    | Expr_overwrite
    | Expr_let_module
    | Expr_let_exception
    | Expr_lazy
    | Expr_object
    | Expr_pack
    | Expr_let_op
    | Expr_unreachable
    | Expr_extension
    | Argument_optional
    | Argument_omitted
    | Functor
    | Type_extensible
    | Def_recursive
    | Def_invalid
    | Def_pattern
    | Def_eval
    | Def_primitive
    | Def_exception
    | Def_module
    | Def_module_type
    | Def_open
    | Def_class
    | Def_class_type
    | Def_include

  let to_string = function
    | Literal_non_integer ->
        "non-integer literal"
    | Pattern_alias ->
        {|"as" pattern|}
    | Pattern_constant ->
        "constant pattern"
    | Pattern_variant ->
        "variant pattern"
    | Pattern_record ->
        "invalid record pattern"
    | Pattern_array ->
        "array pattern"
    | Pattern_or ->
        "disjunction pattern"
    | Pattern_lazy ->
        {|"lazy" pattern|}
    | Pattern_guard ->
        "guard expression"
    | Pattern_constr ->
        "invalid constructor pattern"
    | Pattern_nested ->
        "nested pattern"
    | Pattern_invalid ->
        "invalid pattern"
    | Pattern_non_trivial ->
        "non-trivial pattern in function parameter"
    | Handler_exception ->
        "exception handler"
    | Expr_let_rec_non_function ->
        "recursive binding must bind a function"
    | Expr_let_mutual ->
        "mutually recursive let-bindings"
    | Expr_for_downward ->
        {|downward "for" loop|}
    | Expr_open ->
        "opened module must be an identifier"
    | Expr_array ->
        "array expression"
    | Expr_try ->
        {|"try" expression|}
    | Expr_variant ->
        "variant expression"
    | Expr_send ->
        "method call"
    | Expr_new ->
        {|"new" expression|}
    | Expr_inst_var ->
        "instance variable"
    | Expr_set_inst_var ->
        "instance variable assignment"
    | Expr_overwrite ->
        "overwrite expression"
    | Expr_let_module ->
        "module binding"
    | Expr_let_exception ->
        "exception binding"
    | Expr_lazy ->
        {|"lazy" expression|}
    | Expr_object ->
        "object expression"
    | Expr_pack ->
        "module expression"
    | Expr_let_op ->
        "binding operator"
    | Expr_unreachable ->
        "unreachable branch"
    | Expr_extension ->
        "extension"
    | Argument_optional ->
        "optional function argument"
    | Argument_omitted ->
        "omitted function argument"
    | Functor ->
        "module functor"
    | Type_extensible ->
        "extensible variant"
    | Def_recursive ->
        "recursive toplevel definition must be a function"
    | Def_invalid ->
        "toplevel definition must be a constant or a function"
    | Def_pattern ->
        "toplevel definition pattern must be a variable"
    | Def_eval ->
        "evaluated expression"
    | Def_primitive ->
        "primitive definition"
    | Def_exception ->
        "exception definition"
    | Def_module ->
        "module definition"
    | Def_module_type ->
        "module type definition"
    | Def_open ->
        "opened module must be an identifier"
    | Def_class ->
        "class definition"
    | Def_class_type ->
        "class type definition"
    | Def_include ->
        {|"include" declaration|}

  let pp ppf t =
    Fmt.string ppf (to_string t)
end

module Error = struct
  type t =
    | Unsupported of Unsupported.t
    | Attribute_overwrite_invalid_payload of Attribute.overwrite_kind
    | Envaux of Envaux.error

  let pp ppf = function
    | Unsupported unsupported ->
        Fmt.pf ppf "unsupported feature: %a"
          Unsupported.pp unsupported
    | Attribute_overwrite_invalid_payload kind ->
        Fmt.pf ppf {|payload of attribute "%s%s" must be %s|}
          Attribute.overwrite
          (Attribute.overwrite_kind_to_string kind)
          begin match kind with
          | Overwrite _ ->
              "an expression"
          | Raw ->
              "of the form library.module.identifier"
          end
    | Envaux err ->
        Fmt.pf ppf "internal Envaux error: %a"
          Envaux.report_error err
end

exception Error of Location.t * Error.t

let error ~loc err =
  raise @@ Error (loc, err)
let unsupported ~loc err =
  error ~loc (Unsupported err)

exception Ignore

let record_is_mutable attrs lbls =
  List.exists (fun lbl -> lbl.Types.ld_mutable = Mutable) lbls ||
  Attribute.has_force_record attrs
let record_type_is_mutable ty =
  let[@warning "-8"] Types.Type_record (lbls, _) = ty.Types.type_kind in
  record_is_mutable ty.type_attributes lbls
let inline_record_type_is_mutable constr_attrs ty =
  let[@warning "-8"] Types.Type_record (lbls, _) = ty.Types.type_kind in
  record_is_mutable constr_attrs lbls

module Context = struct
  type t =
    { mutable module_: string
    ; mutable env: Env.t
    ; final_env: Env.t
    ; global_names: int Name.Hashtbl.t
    ; global_ids: Spath.t Ident.Tbl.t
    ; mutable locals: Ident.Set.t
    ; dependencies: (string, string Hashset.t) Hashtbl.t
    }

  let create mod_ final_env =
    { module_= mod_
    ; env= Env.empty
    ; final_env
    ; global_names= Name.Hashtbl.create ()
    ; global_ids= Ident.Tbl.create 17
    ; locals= Ident.Set.empty
    ; dependencies= Hashtbl.create ()
    }

  let env t =
    t.env
  let update_env t env =
    t.env <- Envaux.env_of_only_summary env

  let find_type t path =
    Env.find_type path t.env

  let find_global t id =
    Ident.Tbl.find t.global_ids id
  let add_global t id =
    let global = Ident.name id in
    let idx = Name.Hashtbl.add_update t.global_names global 0 ((+) 1) in
    let global =
      let[@warning "-8"] Some cnt = Env.find_value_index id t.final_env in
      if cnt = 0 then
        global
      else
        global ^ Int.to_string_subscript idx
    in
    Ident.Tbl.add t.global_ids id (Spath.of_list [t.module_; global]) ;
    global

  let mem_local t id =
    Ident.Set.mem id t.locals
  let add_local t id =
    t.locals <- Ident.Set.add id t.locals
  let save_locals t =
    let locals = t.locals in
    fun () -> t.locals <- locals

  let dependencies t =
    t.dependencies
  let add_dependency' t lib mod_ =
    match Hashtbl.find_opt t.dependencies lib with
    | None ->
        let mods = Hashset.singleton mod_ in
        Hashtbl.add t.dependencies lib mods
    | Some mods ->
        Hashset.add mods mod_
  let add_dependency t (lib, mod_) =
    add_dependency' t lib mod_
  let rec add_dependency_from_path t ~loc (path : Path.t) =
    match path with
    | Pident _ ->
        ()
    | Pdot (path', _) ->
        begin match Path.to_list path' with
        | None ->
            unsupported ~loc Functor
        | Some (id, path') ->
            let lib = id |> Ident.name |> String.uncapitalize_ascii in
            let mod_ =
              match path' with
              | [] ->
                  lib
              | mod_ :: _ ->
                  String.uncapitalize_ascii mod_
            in
            add_dependency' t lib mod_
        end
    | Papply _ ->
        unsupported ~loc Functor
    | Pextra_ty (path, _) ->
        add_dependency_from_path t ~loc path
  let add_dependency_from_type t ~loc typ =
    match Types.get_desc typ with
    | Tconstr (path, _, _) ->
        add_dependency_from_path t ~loc path ;
        path
    | _ ->
        assert false
  let add_dependency_from_constructor t ~loc (constr : Data_types.constructor_description) =
    add_dependency_from_type t ~loc constr.cstr_res
  let add_dependency_from_label t ~loc (lbl : Data_types.label_description) =
    add_dependency_from_type t ~loc lbl.lbl_res

  let rec resolve_path t ~loc (path : Path.t) =
    match path with
    | Pident id ->
        if mem_local t id then
          Local (Ident.name id)
        else
          Global (find_global t id)
    | Pdot (path', global) ->
        begin match Path.Map.find_opt path Builtin.paths with
        | Some (expr, dep) ->
            Option.iter (add_dependency t) dep ;
            expr
        | None ->
            match Path.to_list path' with
            | None ->
                unsupported ~loc Functor
            | Some (id, path') ->
                let lib = id |> Ident.name |> String.uncapitalize_ascii in
                let mod_, path' =
                  match path' with
                  | [] ->
                      lib, [lib]
                  | mod_ :: _ ->
                      String.uncapitalize_ascii mod_, path'
                in
                add_dependency' t lib mod_ ;
                let path' = List.map String.uncapitalize_ascii path' in
                Global (Spath.of_list (path' @ [global]))
        end
    | Papply _ ->
        unsupported ~loc Functor
    | Pextra_ty (path, _) ->
        resolve_path t ~loc path
end

let transl_open_declaration ~loc ~err (open_ : Typedtree.open_declaration) =
  match open_.open_expr.mod_desc with
  | Tmod_ident _ ->
      ()
  | _ ->
      unsupported ~loc err

let rec pattern_is_neutral (pat : Typedtree.pattern) =
  match pat.pat_desc with
  | Tpat_any ->
      true
  | Tpat_tuple pats ->
      List.for_all (fun (_, pat) -> pattern_is_neutral pat) pats
  | Tpat_record (pats, Closed) ->
      List.for_all (fun (_, _, pat) -> pattern_is_neutral pat) pats
  | Tpat_construct (_, constr, pats, _) ->
      constr.cstr_consts + constr.cstr_nonconsts = 1 &&
      List.for_all pattern_is_neutral pats
  | _ ->
      false
let rec pattern_to_binder ~ctx ~err (pat : Typedtree.pattern) =
  match pat.pat_desc with
  | Tpat_any ->
      None
  | Tpat_var (id, _, _) ->
      Context.add_local ctx id ;
      Some (Ident.name id)
  | Tpat_alias (pat, id, _, _, _) ->
      if pattern_is_neutral pat then (
        Context.add_local ctx id ;
        Some (Ident.name id)
      ) else (
        unsupported ~loc:pat.pat_loc err
      )
  | Tpat_tuple pats ->
      if List.for_all (fun (_, pat) -> pattern_is_neutral pat) pats then
        None
      else
        unsupported ~loc:pat.pat_loc err
  | Tpat_record ((_, { lbl_repres= Record_unboxed _; _ }, pat) :: _, _) ->
      pattern_to_binder ~ctx ~err pat
  | Tpat_construct (_, { cstr_tag= Cstr_unboxed; _ }, pats, _) ->
      let[@warning "-8"] [pat] = pats in
      pattern_to_binder ~ctx ~err pat
  | Tpat_construct (_, constr, pats, _) ->
      if constr.cstr_consts + constr.cstr_nonconsts = 1
      && List.for_all pattern_is_neutral pats
      then
        None
      else
        unsupported ~loc:pat.pat_loc err
  | _ ->
      unsupported ~loc:pat.pat_loc err

let rec transl_pattern ~ctx (pat : Typedtree.pattern) =
  match pat.pat_desc with
  | Tpat_any ->
      None
  | Tpat_var (id, _, _) ->
      Context.add_local ctx id ;
      Some (Pat_var (Ident.name id))
  | Tpat_tuple pats ->
      let bdrs = List.map (fun (_, pat) -> pattern_to_binder ~ctx ~err:Pattern_nested pat) pats in
      Some (Pat_tuple bdrs)
  | Tpat_record ((_, { lbl_repres= Record_unboxed _; _ }, pat) :: _, _) ->
      transl_pattern ~ctx pat
  | Tpat_record (((_, lbl, _) :: _) as pats, Closed) ->
      let[@warning "-8"] Types.Tconstr (rcd, _, _) = Types.get_desc lbl.lbl_res in
      if record_type_is_mutable (Context.find_type ctx rcd) then
        unsupported ~loc:pat.pat_loc Pattern_record ;
      let bdrs = List.map (fun (_, _, pat) -> pattern_to_binder ~ctx ~err:Pattern_nested pat) pats in
      Some (Pat_tuple bdrs)
  | Tpat_record _ ->
      unsupported ~loc:pat.pat_loc Pattern_record
  | Tpat_construct (_, { cstr_tag= Cstr_unboxed; _ }, pats, _) ->
      let[@warning "-8"] [pat] = pats in
      transl_pattern ~ctx pat
  | Tpat_construct (lid, constr, pats, _) ->
      let bdrs = List.map (pattern_to_binder ~ctx ~err:Pattern_nested) pats in
      if Longident.Map.mem lid.txt Builtin.constrs then
        unsupported ~loc:lid.loc Pattern_constr ;
      let tag = Option.get_lazy (fun () -> unsupported ~loc:lid.loc Functor) (Longident.last lid.txt) in
      let _variant = Context.add_dependency_from_constructor ctx ~loc:lid.loc constr in
      Some (Pat_constr (tag, bdrs))
  | Tpat_alias _ ->
      unsupported ~loc:pat.pat_loc Pattern_alias
  | Tpat_constant _ ->
      unsupported ~loc:pat.pat_loc Pattern_constant
  | Tpat_variant _ ->
      unsupported ~loc:pat.pat_loc Pattern_variant
  | Tpat_array _ ->
      unsupported ~loc:pat.pat_loc Pattern_array
  | Tpat_or _ ->
      unsupported ~loc:pat.pat_loc Pattern_or
  | Tpat_lazy _ ->
      unsupported ~loc:pat.pat_loc Pattern_lazy

let check_argument_label ~loc (lbl : Asttypes.arg_label) =
  match lbl with
  | Nolabel
  | Labelled _ ->
      ()
  | Optional _ ->
      unsupported ~loc Argument_optional
let transl_expression_field ~ctx ~loc expr (lbl : Data_types.label_description)  =
  let fld = lbl.lbl_name in
  let rcd = Context.add_dependency_from_label ctx ~loc lbl in
  if record_type_is_mutable (Context.find_type ctx rcd) then
    Record_get (expr, fld)
  else
    Proj (expr, fld)
let rec transl_expression ~ctx (expr : Typedtree.expression) =
  match expr.exp_desc with
  | Texp_ident (path, _, _) ->
      transl_expression_ident ~ctx ~loc:expr.exp_loc path
  | Texp_constant (Const_int int) ->
      Int int
  | Texp_constant _ ->
      unsupported ~loc:expr.exp_loc Literal_non_integer
  | Texp_let (rec_flag, [bdg], expr2) ->
      let expr1 = transl_expression ~ctx bdg.vb_expr in
      let restore_locals = Context.save_locals ctx in
      begin match transl_pattern ~ctx bdg.vb_pat with
      | None ->
          let expr2 = transl_expression ~ctx expr2 in
          Seq (expr1, expr2)
      | Some pat ->
          match expr1 with
          | Fun (bdrs, expr1) ->
              let[@warning "-8"] Pat_var local = pat in
              let expr2 = transl_expression ~ctx expr2 in
              restore_locals () ;
              Letrec (rec_flag, local, bdrs, expr1, expr2)
          | _ ->
              if rec_flag = Recursive then
                unsupported ~loc:bdg.vb_loc Expr_let_rec_non_function ;
              let expr2 = transl_expression ~ctx expr2 in
              restore_locals () ;
              Let (pat, expr1, expr2)
      end
  | Texp_let (_, _, _) ->
      unsupported ~loc:expr.exp_loc Expr_let_mutual
  | Texp_function (params, body) ->
      let restore_locals = Context.save_locals ctx in
      let bdrs =
        List.map (fun (param : Typedtree.function_param) ->
          check_argument_label ~loc:param.fp_loc param.fp_arg_label ;
          let[@warning "-8"] Typedtree.Tparam_pat pat = param.fp_kind in
          pattern_to_binder ~ctx ~err:Pattern_non_trivial pat
        ) params
      in
      begin match body with
      | Tfunction_body expr ->
          let expr = transl_expression ~ctx expr in
          restore_locals () ;
          Fun (bdrs, expr)
      | Tfunction_cases { cases= brs; param= id; _ } ->
          Context.add_local ctx id ;
          let brs, fb = transl_branches ~ctx brs in
          restore_locals () ;
          let local = Ident.name id in
          Fun (bdrs @ [Some local], Match (Local local, brs, fb))
      end
  | Texp_apply (expr', exprs) ->
      let arguments () =
        List.map (fun (lbl, expr') ->
          check_argument_label ~loc:expr.exp_loc lbl ;
          match (expr' : Typedtree.apply_arg) with
          | Omitted _ ->
              unsupported ~loc:expr.exp_loc Argument_omitted
          | Arg expr' ->
              transl_expression ~ctx expr'
        ) exprs
      in
      let default exprs =
        let expr' = transl_expression ~ctx expr' in
        Apply (expr', exprs)
      in
      begin match expr'.exp_desc with
      | Texp_ident (path', _, _) ->
          begin match Path.Map.find_opt path' Builtin.apps with
          | None ->
              default (arguments ())
          | Some (mk_expr, dep) ->
              Option.iter (Context.add_dependency ctx) dep ;
              match mk_expr with
              | Opaque expr ->
                  expr
              | Transparent mk_expr ->
                  let exprs = arguments () in
                  match mk_expr exprs with
                  | Some expr ->
                      expr
                  | None ->
                      default exprs
          end
      | _ ->
          default (arguments ())
      end
  | Texp_ifthenelse (expr1, expr2, expr3) ->
      let expr1 = transl_expression ~ctx expr1 in
      begin match expr1, expr2.exp_desc, expr3 with
      | Unop (Unop_neg, expr1), Texp_apply ({ exp_desc= Texp_ident (path, _, _); _ }, _), None
        when Path.Set.mem path Builtin.raising ->
          Context.add_dependency ctx Dependency.assume ;
          Apply (Global Spath.Builtin.assume, [expr1])
      | _ ->
          let expr2 = transl_expression ~ctx expr2 in
          let expr3 = Option.map (transl_expression ~ctx) expr3 in
          If (expr1, expr2, expr3)
      end
  | Texp_sequence (expr1, expr2) ->
      let expr1 = transl_expression ~ctx expr1 in
      let expr1 =
        match expr1 with
        | Seq (expr1, Tuple []) ->
            expr1
        | _ ->
            expr1
      in
      let expr2 = transl_expression ~ctx expr2 in
      Seq (expr1, expr2)
  | Texp_while (expr1, expr2) ->
      let expr1 = transl_expression ~ctx expr1 in
      let expr2 = transl_expression ~ctx expr2 in
      While (expr1, expr2)
  | Texp_for (id, pat, expr1, expr2, Upto, expr3) ->
      let bdr =
        match pat.ppat_desc with
        | Ppat_any ->
            None
        | Ppat_var { txt= local; _ } ->
            Some local
        | _ ->
            assert false
      in
      let expr1 = transl_expression ~ctx expr1 in
      let expr2 = transl_expression ~ctx expr2 in
      let expr2 =
        match expr2 with
        | Binop (Binop_minus, expr2, Int 1) ->
            expr2
        | _ ->
            Binop (Binop_plus, expr2, Int 1)
      in
      let restore_locals = Context.save_locals ctx in
      Context.add_local ctx id ;
      let expr3 = transl_expression ~ctx expr3 in
      restore_locals () ;
      For (bdr, expr1, expr2, expr3)
  | Texp_for (_, _, _, _, Downto, _) ->
      unsupported ~loc:expr.exp_loc Expr_for_downward
  | Texp_tuple exprs ->
      let exprs = List.map (fun (_, e) -> transl_expression ~ctx e) exprs in
      Tuple exprs
  | Texp_record rcd ->
      transl_expression_record ~ctx ~loc:expr.exp_loc rcd.fields rcd.extended_expression (fun exprs ->
        match rcd.representation with
        | Record_unboxed _ ->
            let[@warning "-8"] [expr] = exprs in
            expr
        | _ ->
            let[@warning "-8"] Types.Tconstr (rcd, _, _) = Types.get_desc expr.exp_type in
            if record_type_is_mutable (Context.find_type ctx rcd) then
              Record exprs
            else
              Tuple exprs
      )
  | Texp_construct (_, { cstr_tag= Cstr_unboxed; _ }, exprs) ->
      let[@warning "-8"] [expr] = exprs in
      transl_expression ~ctx expr
  | Texp_construct (lid, constr, exprs) ->
      begin match Longident.Map.find_opt lid.txt Builtin.constrs with
      | Some expr ->
          assert (exprs = []) ;
          expr
      | None ->
          let tag = Option.get_lazy (fun () -> unsupported ~loc:lid.loc Functor) (Longident.last lid.txt) in
          let _variant = Context.add_dependency_from_constructor ctx ~loc:lid.loc constr in
          let mk_immutable exprs =
            Constr (Immutable_nongenerative, tag, exprs)
          in
          match constr.cstr_inlined with
          | None ->
              let exprs = List.map (transl_expression ~ctx) exprs in
              mk_immutable exprs
          | Some ty ->
              let[@warning "-8"] [expr] = exprs in
              match expr.exp_desc with
              | Texp_ident (path, _, _) ->
                  transl_expression_ident ~ctx ~loc:expr.exp_loc path
              | Texp_record rcd ->
                  transl_expression_record ~ctx ~loc:expr.exp_loc rcd.fields rcd.extended_expression (fun exprs ->
                    if inline_record_type_is_mutable constr.cstr_attributes ty then
                      Constr (Mutable, tag, exprs)
                    else
                      mk_immutable exprs
                  )
              | _ ->
                  assert false
      end
  | Texp_match (expr, brs, _, _) ->
      let expr = transl_expression ~ctx expr in
      let brs, fb = transl_branches ~ctx brs in
      Match (expr, brs, fb)
  | Texp_atomic_loc (expr, lid, lbl) ->
      let expr = transl_expression ~ctx expr in
      let fld = lbl.lbl_name in
      let _rcd = Context.add_dependency_from_label ctx ~loc:lid.loc lbl in
      (* A descriptor written inline, [%atomic.loc t.f], reaches the printer
         without passing through the builtin tables; if it lands under a
         read-modify-write it is printed with a wrapper, so require it here
         too. Over-approximates when the descriptor is used first-class. *)
      Context.add_dependency ctx Dependency.atomic_loc ;
      Atomic_loc (expr, fld)
  | Texp_field (expr, lid, lbl) ->
      let expr = transl_expression ~ctx expr in
      transl_expression_field ~ctx ~loc:lid.loc expr lbl
  | Texp_setfield (expr1, lid, lbl, expr2) ->
      let expr1 = transl_expression ~ctx expr1 in
      let fld = lbl.lbl_name in
      let _rcd = Context.add_dependency_from_label ctx ~loc:lid.loc lbl in
      let expr2 = transl_expression ~ctx expr2 in
      Record_set (expr1, fld, expr2)
  | Texp_assert ({ exp_desc= Texp_construct (_, { cstr_name= "false"; _ }, _); _ }, _) ->
      Fail
  | Texp_assert (expr, _) ->
      Context.add_dependency ctx Dependency.assert_ ;
      let expr = transl_expression ~ctx expr in
      Apply (Global Spath.Builtin.assert_, [expr])
  | Texp_open (open_, expr) ->
      transl_open_declaration ~loc:expr.exp_loc ~err:Expr_open open_ ;
      transl_expression ~ctx expr
  | Texp_array _ ->
      unsupported ~loc:expr.exp_loc Expr_array
  | Texp_try _ ->
      unsupported ~loc:expr.exp_loc Expr_try
  | Texp_variant _ ->
      unsupported ~loc:expr.exp_loc Expr_variant
  | Texp_send _ ->
      unsupported ~loc:expr.exp_loc Expr_send
  | Texp_new _ ->
      unsupported ~loc:expr.exp_loc Expr_new
  | Texp_instvar _ ->
      unsupported ~loc:expr.exp_loc Expr_inst_var
  | Texp_setinstvar _ ->
      unsupported ~loc:expr.exp_loc Expr_set_inst_var
  | Texp_override _ ->
      unsupported ~loc:expr.exp_loc Expr_overwrite
  | Texp_letmodule _ ->
      unsupported ~loc:expr.exp_loc Expr_let_module
  | Texp_letexception _ ->
      unsupported ~loc:expr.exp_loc Expr_let_exception
  | Texp_lazy _ ->
      unsupported ~loc:expr.exp_loc Expr_lazy
  | Texp_object _ ->
      unsupported ~loc:expr.exp_loc Expr_object
  | Texp_pack _ ->
      unsupported ~loc:expr.exp_loc Expr_pack
  | Texp_letop _ ->
      unsupported ~loc:expr.exp_loc Expr_let_op
  | Texp_unreachable ->
      unsupported ~loc:expr.exp_loc Expr_unreachable
  | Texp_extension_constructor _ ->
      unsupported ~loc:expr.exp_loc Expr_extension
and transl_expression_ident ~ctx ~loc path =
  Context.resolve_path ctx ~loc path
and transl_expression_record ~ctx ~loc flds ext_expr mk_expr =
  let ext_expr =
    match ext_expr with
    | None ->
        Either.Left Name.temporary
    | Some ext_expr ->
        match transl_expression ~ctx ext_expr with
        | Local local ->
            Left local
        | ext_expr ->
            Right ext_expr
  in
  let exprs =
    Array.fold_right (fun (lbl, def) acc ->
      let expr =
        match def with
        | Typedtree.Kept _ ->
            transl_expression_field ~ctx ~loc (Local (Either.get_left ~right:Name.temporary ext_expr)) lbl
        | Overridden (_, expr) ->
            transl_expression ~ctx expr
      in
      expr :: acc
    ) flds []
  in
  let expr = mk_expr exprs in
  match ext_expr with
  | Left _ ->
      expr
  | Right ext_expr ->
      Let (Pat_var Name.temporary, ext_expr, expr)
and transl_branches : type a. ctx:Context.t -> a Typedtree.case list -> branch list * fallback option = fun ~ctx brs ->
  let rec aux1 acc = function
    | [] ->
        acc, None
    | br :: brs ->
        Option.iter (fun expr -> unsupported ~loc:expr.Typedtree.exp_loc Pattern_guard) br.Typedtree.c_guard ;
        let restore_locals = Context.save_locals ctx in
        let pat = br.c_lhs in
        let pat =
          match (pat.pat_desc : a Typedtree.pattern_desc) with
          | Tpat_value pat ->
              (pat :> Typedtree.(value general_pattern))
          | Tpat_exception _ ->
              unsupported ~loc:pat.pat_loc Handler_exception
          | Tpat_or _ ->
              unsupported ~loc:pat.pat_loc Pattern_or
          | Tpat_any ->
              pat
          | Tpat_var _ ->
              pat
          | Tpat_alias _ ->
              pat
          | Tpat_constant _ ->
              pat
          | Tpat_tuple _ ->
              pat
          | Tpat_construct _ ->
              pat
          | Tpat_variant _ ->
              pat
          | Tpat_record _ ->
              pat
          | Tpat_array _ ->
              pat
          | Tpat_lazy _ ->
              pat
        in
        let pat, bdr =
          match pat.pat_desc with
          | Tpat_alias (pat, local, _, _, _) ->
              Context.add_local ctx local ;
              pat, Some (Ident.name local)
          | _ ->
              pat, None
        in
        let rec aux2 (pat : Typedtree.pattern) bdr =
          match pat.pat_desc with
          | Tpat_any ->
              let expr = transl_expression ~ctx br.c_rhs in
              restore_locals () ;
              acc, Some { fallback_as= bdr; fallback_expr= expr }
          | Tpat_var (id, _, _) ->
              Context.add_local ctx id ;
              let expr = transl_expression ~ctx br.c_rhs in
              restore_locals () ;
              let local = Ident.name id in
              begin match bdr with
              | None ->
                  acc, Some { fallback_as= Some local; fallback_expr= expr }
              | Some local' ->
                  acc, Some { fallback_as= bdr; fallback_expr= Let (Pat_var local, Local local', expr) }
              end
          | Tpat_record ((_, { lbl_repres= Record_unboxed _; _ }, pat) :: _, _) ->
              aux2 pat bdr
          | Tpat_construct (_, { cstr_tag= Cstr_unboxed; _ }, pats, _) ->
              let[@warning "-8"] [pat] = pats in
              aux2 pat bdr
          | Tpat_construct (lid, constr, pats, _) ->
              if Longident.Map.mem lid.txt Builtin.constrs then
                unsupported ~loc:lid.loc Pattern_constr ;
              let tag = Option.get_lazy (fun () -> unsupported ~loc:lid.loc Functor) (Longident.last lid.txt) in
              let _variant = Context.add_dependency_from_constructor ctx ~loc:lid.loc constr in
              let bdrs, bdr, expr =
                match constr.cstr_inlined with
                | None ->
                    let bdrs = List.map (pattern_to_binder ~ctx ~err:Pattern_invalid) pats in
                    let bdrs =
                      match bdrs with
                      | [None] ->
                          List.make constr.cstr_arity None
                      | _ ->
                          bdrs
                    in
                    let expr = transl_expression ~ctx br.c_rhs in
                    bdrs, bdr, expr
                | Some ty ->
                    let[@warning "-8"] [pat] = pats in
                    match pat.pat_desc with
                    | Tpat_any ->
                        let expr = transl_expression ~ctx br.c_rhs in
                        let[@warning "-8"] Types.Type_record (lbls, _) = ty.type_kind in
                        let bdrs = List.make (List.length lbls) None in
                        bdrs, bdr, expr
                    | Tpat_var (id, _, _) ->
                        Context.add_local ctx id ;
                        let expr = transl_expression ~ctx br.c_rhs in
                        let bdr, expr =
                          let local = Ident.name id in
                          match bdr with
                          | None ->
                              Some local, expr
                          | Some local' ->
                              bdr, Let (Pat_var local, Local local', expr)
                        in
                        let[@warning "-8"] Types.Type_record (lbls, _) = ty.type_kind in
                        let bdrs = List.make (List.length lbls) None in
                        bdrs, bdr, expr
                    | Tpat_record (pats, Closed) ->
                        if inline_record_type_is_mutable constr.cstr_attributes ty then
                          unsupported ~loc:pat.pat_loc Pattern_invalid ;
                        let bdrs = List.map (fun (_, _, pat) -> pattern_to_binder ~ctx ~err:Pattern_invalid pat) pats in
                        let expr = transl_expression ~ctx br.c_rhs in
                        bdrs, bdr, expr
                    | _ ->
                        unsupported ~loc:pat.pat_loc Pattern_invalid
              in
              restore_locals () ;
              aux1 ({ branch_tag= tag; branch_fields= bdrs; branch_as= bdr; branch_expr= expr } :: acc) brs
          | _ ->
              unsupported ~loc:pat.pat_loc Pattern_invalid
        in
        aux2 pat bdr
  in
  let brs, fb = aux1 [] brs in
  List.rev brs, fb

let transl_value_binding ~ctx rec_flag bdgs (bdg : Typedtree.value_binding) global id rec_flag' expr =
  let restore_locals = Context.save_locals ctx in
  begin match rec_flag, rec_flag' with
  | Recursive, _ ->
      List.iter (fun (_, _, id, _) -> Context.add_local ctx id) bdgs
  | Nonrecursive, Recursive ->
      Context.add_local ctx id
  | Nonrecursive, Nonrecursive ->
      ()
  end ;
  let expr = transl_expression ~ctx expr in
  restore_locals () ;
  let rec_ = rec_flag = Recursive || rec_flag' = Recursive in
  match expr with
  | Fun (bdrs, expr) ->
      if rec_ then
        Val_recs [global, Ident.name id, bdrs, expr]
      else
        Val_fun (global, bdrs, expr)
  | _ ->
      if rec_ then
        unsupported ~loc:bdg.vb_loc Def_recursive ;
      if expression_is_value expr then
        Val_expr (global, expr)
      else
        unsupported ~loc:bdg.vb_loc Def_invalid
let transl_value_binding ~ctx mod_ rec_flag bdgs bdg global id loc =
  match Attribute.has_overwrite bdg.Typedtree.vb_attributes with
  | None ->
      transl_value_binding ~ctx rec_flag bdgs bdg global id Nonrecursive bdg.vb_expr
  | Some (Overwrite rec_flag' as kind, attr) ->
      begin match attr.attr_payload with
      | PStr [{ pstr_desc= Pstr_eval (expr, _); _ }] ->
          let env = Context.env ctx in
          let add env id =
            let val_descr : Types.value_description =
              { val_type= Ctype.newvar ()
              ; val_attributes= []
              ; val_kind= Val_reg
              ; val_loc= loc
              ; val_uid= Types.Uid.of_compilation_unit_id (Ident.create_persistent mod_)
              }
            in
            Env.add_value id val_descr env
          in
          let env =
            match rec_flag, rec_flag' with
            | Recursive, _ ->
                List.fold_left (fun env (_, _, id, _) -> add env id) env bdgs
            | Nonrecursive, Recursive ->
                add env id
            | Nonrecursive, Nonrecursive ->
                env
          in
          transl_value_binding ~ctx rec_flag bdgs bdg global id rec_flag' (Typecore.type_expression env expr)
      | _ ->
          error ~loc:attr.attr_loc (Attribute_overwrite_invalid_payload kind)
      end
  | Some (Raw, attr) ->
      begin match attr.attr_payload with
      | PStr [{ pstr_desc= Pstr_eval ({ pexp_desc= Pexp_constant { pconst_desc= Pconst_string (raw, _, _); _ }; _ }, _); _ }] ->
          begin match String.split_on_char '.' raw with
          | [lib; mod_; global'] ->
              Context.add_dependency' ctx lib mod_ ;
              Val_expr (global, Global (Spath.of_list [mod_; global']))
          | _ ->
              error ~loc:attr.attr_loc (Attribute_overwrite_invalid_payload Raw)
          end
      | _ ->
          error ~loc:attr.attr_loc (Attribute_overwrite_invalid_payload Raw)
      end

let transl_value_bindings ~ctx mod_ rec_flag bdgs =
  let bdgs =
    List.map (fun (bdg : Typedtree.value_binding) ->
      match bdg.vb_pat.pat_desc with
      | Tpat_var (id, { loc; _ }, _) ->
          let global = Context.add_global ctx id in
          bdg, global, id, loc
      | _ ->
          unsupported ~loc:bdg.vb_pat.pat_loc Def_pattern
    ) bdgs
  in
  let[@warning "-8"] (bdg, _, _, _) :: _ = bdgs in
  if Attribute.has_ignore bdg.vb_attributes then
    []
  else if Attribute.has_opaque bdg.vb_attributes then
    List.map (fun (_, global, _, _) -> Val_opaque global) bdgs
  else
    let vals =
      List.map (fun (bdg, global, id, loc) ->
        transl_value_binding ~ctx mod_ rec_flag bdgs bdg global id loc
      ) bdgs
    in
    match rec_flag with
    | Nonrecursive ->
        vals
    | Recursive ->
        let recs = List.concat_map (function Val_recs recs -> recs | _ -> assert false) vals in
        [Val_recs recs]

let transl_type_declaration_record attrs lbls =
  let is_mut = record_is_mutable attrs lbls in
  let lbls = List.map (fun lbl -> Ident.name lbl.Types.ld_id) lbls in
  if is_mut then
    Type_record lbls
  else
    Type_product lbls
let transl_type_declaration (ty : Typedtree.type_declaration) =
  let gid = ty.typ_name.txt in
  match ty.typ_type.type_kind with
  | Type_abstract _ ->
      []
  | Type_record (_, Record_unboxed _) ->
      []
  | Type_record (lbls, _) ->
      let ty = transl_type_declaration_record ty.typ_attributes lbls in
      [Type (gid, ty)]
  | Type_variant (_, Variant_unboxed) ->
      []
  | Type_variant (constrs, _) ->
      let tags, defs =
        List.fold_right (fun (constr : Types.constructor_declaration) (tags, defs) ->
          let tag = Ident.name constr.cd_id in
          let defs =
            match constr.cd_args with
            | Cstr_record lbls ->
                let ty = transl_type_declaration_record constr.cd_attributes lbls in
                Type (Printf.sprintf "%s.%s" gid tag, ty) :: defs
            | _ ->
                defs
          in
          tag :: tags, defs
        ) constrs ([], [])
      in
      Type (gid, Type_variant tags) :: defs
  | Type_open ->
      unsupported ~loc:ty.typ_loc Type_extensible

let transl_structure_item ~ctx mod_ (str_item : Typedtree.structure_item) =
  match str_item.str_desc with
  | Tstr_value (rec_flag, bdgs) ->
      let vals = transl_value_bindings ~ctx mod_ rec_flag bdgs in
      List.map (fun val_ -> Val val_) vals
  | Tstr_type (_, tys) ->
      List.concat_map transl_type_declaration tys
  | Tstr_open open_ ->
      transl_open_declaration ~loc:str_item.str_loc ~err:Def_open open_ ;
      []
  | Tstr_attribute attr ->
      if Attribute.has_ignore [attr] then
        raise Ignore ;
      []
  | Tstr_eval _ ->
      unsupported ~loc:str_item.str_loc Def_eval
  | Tstr_primitive _ ->
      unsupported ~loc:str_item.str_loc Def_primitive
  | Tstr_typext _ ->
      unsupported ~loc:str_item.str_loc Type_extensible
  | Tstr_exception _ ->
      unsupported ~loc:str_item.str_loc Def_exception
  | Tstr_module _
  | Tstr_recmodule _ ->
      unsupported ~loc:str_item.str_loc Def_module
  | Tstr_modtype _ ->
      unsupported ~loc:str_item.str_loc Def_module_type
  | Tstr_class _ ->
      unsupported ~loc:str_item.str_loc Def_class
  | Tstr_class_type _ ->
      unsupported ~loc:str_item.str_loc Def_class_type
  | Tstr_include _ ->
      unsupported ~loc:str_item.str_loc Def_include
let transl_structure_item ~ctx mod_ (str_item : Typedtree.structure_item) =
  Context.update_env ctx str_item.str_env ;
  transl_structure_item ~ctx mod_ str_item

let transl_structure ~lib ~mod_ (str : Typedtree.structure) =
  let final_env =
    try
      Envaux.env_of_only_summary str.str_final_env
    with Envaux.Error err ->
      error ~loc:Location.none (Envaux err)
  in
  let ctx = Context.create mod_ final_env in
  let definitions = List.concat_map (transl_structure_item ~ctx mod_) str.str_items in
  let dependencies = Context.dependencies ctx in
  { library= lib
  ; module_= mod_
  ; dependencies
  ; definitions
  }
