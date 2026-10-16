open Implementation

let pp_boolean ppf =
  Fmt.pf ppf "%B"
let pp_integer ppf int =
  if int < 0 then
    Fmt.pf ppf "(%i)" int
  else
    Fmt.pf ppf "%i" int

let pp_local ppf local =
  Fmt.pf ppf {|"%s"|} local

let pp_binder ppf = function
  | None ->
      Fmt.pf ppf "<>"
  | Some local ->
      pp_local ppf local

let pp_pattern ppf = function
  | Pat_var local ->
      pp_local ppf local
  | Pat_tuple bdrs ->
      Fmt.(list ~sep:(const string ", ") pp_binder) ppf bdrs
  | Pat_constr (tag, bdrs) ->
      Fmt.pf ppf "‘%s %a"
        tag
        Fmt.(list ~sep:(const string ", ") pp_binder) bdrs

let pp_unop ppf op =
  Fmt.char ppf
    begin match op with
    | Unop_neg ->
        '~'
    | Unop_minus ->
        '-'
    end

let pp_binop ppf op =
  Fmt.string ppf
    begin match op with
    | Binop_plus ->
        "+"
    | Binop_minus ->
        "-"
    | Binop_mult ->
        "*"
    | Binop_quot ->
        "`quot`"
    | Binop_rem ->
        "`rem`"
    | Binop_land ->
        "`land`"
    | Binop_lor ->
        "`lor`"
    | Binop_lsl ->
        "`lsl`"
    | Binop_lsr ->
        "`lsr`"
    | Binop_eq ->
        "=="
    | Binop_ne ->
        "!="
    | Binop_le ->
        "≤"
    | Binop_lt ->
        "<"
    | Binop_ge ->
        "≥"
    | Binop_gt ->
        ">"
    | Binop_and ->
        "and"
    | Binop_or ->
        "or"
    | Binop_structeq ->
        "="
    | Binop_structne ->
        "≠"
    end

type associativity =
  | Left
  | Right
let associativity = function
  | Binop_lsl
  | Binop_lsr ->
      Right
  | Binop_plus
  | Binop_minus
  | Binop_mult
  | Binop_quot
  | Binop_rem
  | Binop_land
  | Binop_lor
  | Binop_eq
  | Binop_ne
  | Binop_le
  | Binop_lt
  | Binop_ge
  | Binop_gt
  | Binop_and
  | Binop_or
  | Binop_structeq
  | Binop_structne ->
      Left

let max_level =
  200
let next_level lvl =
  lvl - 1
let level = function
  | Constr (_, "::", _) ->
      60
  | Global _
  | Local _
  | If _
  | While _
  | For _
  | Tuple _
  | Record _
  | Constr _
  | Match _
  | Fail
  | Skip ->
      1
  | Proj _ ->
      2
  | Bool _
  | Int _ ->
      8
  | Ref_get _
  | Record_get _
  | Atomic_loc _ ->
      9
  | Apply _
  | Alloc _
  | Ref _
  | Is_immediate _
  | Get_tag _
  | Get_size _
  | Load _
  | Store _
  | Xchg _
  | Cas _
  | Faa _ ->
      10
  | Binop (Binop_lsl, _, _)
  | Binop (Binop_lsr, _, _) ->
      30
  | Binop (Binop_land, _, _) ->
      31
  | Binop (Binop_lor, _, _) ->
      32
  | Unop (Unop_minus, _)
  | Binop (Binop_quot, _, _)
  | Binop (Binop_rem, _, _) ->
      35
  | Binop (Binop_mult, _, _) ->
      40
  | Binop (Binop_plus, _, _)
  | Binop (Binop_minus, _, _) ->
      50
  | Binop (Binop_eq, _, _)
  | Binop (Binop_ne, _, _)
  | Binop (Binop_le, _, _)
  | Binop (Binop_lt, _, _)
  | Binop (Binop_ge, _, _)
  | Binop (Binop_gt, _, _)
  | Binop (Binop_structeq, _, _)
  | Binop (Binop_structne, _, _) ->
      70
  | Unop (Unop_neg, _) ->
      75
  | Binop (Binop_and, _, _) ->
      76
  | Binop (Binop_or, _, _) ->
      77
  | Ref_set _
  | Record_set _ ->
      80
  | Seq _ ->
      100
  | Let _
  | Letrec _
  | Fun _ ->
      max_level

(* Mizzle spells the atomicity of a field access out in the constructor. *)
let pp_atomicity = function
  | Atomic ->
      "Atomic"
  | Not_atomic ->
      "NotAtomic"
(* ...and, for the notations, as a superscript suffix: [!ᵃᵗ e], [e <-ᵃᵗ v]. *)
let pp_atomicity_suffix = function
  | Atomic ->
      "ᵃᵗ"
  | Not_atomic ->
      ""

let rec pp_expression' lvl ppf = function
  | Global spath ->
      Spath.pp ppf spath
  | Local local ->
      pp_local ppf local
  | Bool bool ->
      pp_boolean ppf bool
  | Int int ->
      pp_integer ppf int
  | Let (pat, expr1, expr2) ->
      Fmt.pf ppf "@[<v>@[<hv>let: %a :=@;<1 2>@[%a@]@;in@]@,%a@]"
        pp_pattern pat
        (pp_expression max_level) expr1
        (pp_expression max_level) expr2
  | Letrec (rec_flag, local, bdrs, expr1, expr2) ->
      Fmt.pf ppf "@[<v>@[<hv>let%s: %a %a :=@;<1 2>@[%a@]@;in@]@,%a@]"
        (match rec_flag with Nonrecursive -> "" | Recursive -> "rec")
        pp_local local
        Fmt.(list ~sep:(const char ' ') pp_binder) bdrs
        (pp_expression max_level) expr1
        (pp_expression max_level) expr2
  | Seq (expr1, expr2) ->
      Fmt.pf ppf "@[<v>@[" ;
      begin match expr1 with
      | If (expr1, expr2, expr3) ->
          pp_expression_if ~force_else:true ppf expr1 expr2 expr3
      | _ ->
          pp_expression (next_level lvl) ppf expr1
      end ;
      Fmt.pf ppf "@] ;;@,%a@]"
        (pp_expression max_level) expr2
  | Fun (bdrs, expr) ->
      Fmt.pf ppf "@[<hv>fun: %a =>@;<1 2>@[%a@]@]"
        Fmt.(list ~sep:(const char ' ') pp_binder) bdrs
        (pp_expression max_level) expr
  | Apply (expr, exprs) ->
      Fmt.pf ppf "@[<hv>@[%a@]%a@]"
        (pp_expression lvl) expr
        Fmt.(
          list ~sep:nop @@ fun ppf ->
            pf ppf "@;<1 2>@[%a@]"
              (pp_expression @@ next_level lvl)
        ) exprs
  | Unop (op, expr) ->
      Fmt.pf ppf "@[<hv>@[%a@]@;@[%a@]@]"
        pp_unop op
        (pp_expression lvl) expr
  | Binop (op, expr1, expr2) ->
      let assoc = associativity op in
      Fmt.pf ppf "@[<hv>@[%a@]@;@[%a@]@;@[%a@]@]"
        (pp_expression @@ if assoc = Left then lvl else next_level lvl) expr1
        pp_binop op
        (pp_expression @@ if assoc = Left then next_level lvl else lvl) expr2
  | If (expr1, expr2, expr3) ->
      pp_expression_if ppf expr1 expr2 expr3
  | While (expr1, expr2) ->
      Fmt.pf ppf "@[<v>@[<hv>while:@;<1 2>@[%a@]@;begin@]@,  @[%a@]@,end@]"
        (pp_expression max_level) expr1
        (pp_expression max_level) expr2
  | For (local, expr1, expr2, expr3) ->
      Fmt.pf ppf "@[<v>@[<hv>for:@;<1 2>@[%a@]@;:=@;<1 2>@[%a@]@;to@;<1 2>@[%a@]@;begin@]@,  @[%a@]@,end@]"
        pp_binder local
        (pp_expression max_level) expr1
        (pp_expression max_level) expr2
        (pp_expression max_level) expr3
  | Alloc (expr1, expr2) ->
      Fmt.pf ppf "@[<hv>Alloc@;<1 2>@[%a@]@;<1 2>@[%a@]@]"
        (pp_expression @@ next_level lvl) expr1
        (pp_expression @@ next_level lvl) expr2
  | Tuple exprs ->
      Fmt.pf ppf "@[<hv>(%a@,)@]"
        Fmt.(
          list ~sep:(any ",@;<1 1>") @@ fun ppf ->
            pf ppf "@[%a@]"
              (pp_expression max_level)
        ) exprs
  | Ref expr ->
      Fmt.pf ppf "@[<hv>ref@;<1 2>@[%a@]@]"
        (pp_expression @@ next_level lvl) expr
  | Record exprs ->
      Fmt.pf ppf "@[<hv>{ %a@;}@]"
        Fmt.(
          list ~sep:(any ",@;<1 2>") @@ fun ppf ->
            pf ppf "@[%a@]"
              (pp_expression max_level)
        ) exprs
  | Constr (_, "[]", _) ->
      Fmt.pf ppf "[]"
  | Constr (_, "::", exprs) ->
      let[@warning "-8"] [expr1; expr2] = exprs in
      Fmt.pf ppf "@[<hv>%a ::@;<1 2>@[%a@]@]"
        (pp_expression @@ next_level lvl) expr1
        (pp_expression lvl) expr2
  | Constr (_, tag, []) ->
      Fmt.pf ppf "§%s"
        tag
  | Constr (flag, tag, exprs) ->
      Fmt.pf ppf "@[<hv>‘%s%s %a@;%s@]"
        tag
        ( match flag with
          | Mutable -> "{"
          | Immutable_nongenerative -> "("
          | Immutable_generative_weak -> "["
          | Immutable_generative_strong -> "@["
        )
        Fmt.(
          list ~sep:(any ",@;<1 2>") @@ fun ppf ->
            pf ppf "@[%a@]"
              (pp_expression max_level)
        ) exprs
        ( match flag with
          | Mutable -> "}"
          | Immutable_nongenerative -> ")"
          | Immutable_generative_weak -> "]"
          | Immutable_generative_strong -> "]"
        )
  | Proj (expr, fld) ->
      Fmt.pf ppf "@[%a@].<%s>"
        (pp_expression lvl) expr
        fld
  | Match (expr, brs, fb) ->
      Fmt.pf ppf "@[<v>@[<hv>match:@;<1 2>@[%a@]@;with@]@,%a%aend@]"
        (pp_expression max_level) expr
        Fmt.(list ~sep:nop pp_branch) brs
        Fmt.(option pp_fallback) fb
  | Ref_get (atm, expr) ->
      Fmt.pf ppf "!%s@[%a@]"
        (pp_atomicity_suffix atm)
        (pp_expression lvl) expr
  | Ref_set (atm, expr1, expr2) ->
      Fmt.pf ppf "@[<hv>@[<hv>@[%a@]@;<1 2><-%s@]@;<1 2>@[%a@]@]"
        (pp_expression @@ next_level lvl) expr1
        (pp_atomicity_suffix atm)
        (pp_expression lvl) expr2
  | Record_get (expr, fld) ->
      Fmt.pf ppf "@[%a@].{%s}"
        (pp_expression lvl) expr
        fld
  | Record_set (expr1, fld, expr2) ->
      Fmt.pf ppf "@[<hv>@[<hv>@[%a@]@;<1 2><-{%s}@]@;<1 2>@[%a@]@]"
        (pp_expression @@ next_level lvl) expr1
        fld
        (pp_expression lvl) expr2
  | Is_immediate expr ->
      Fmt.pf ppf "@[<hv>IsImmediate@;<1 2>@[%a@]@]"
        (pp_expression @@ next_level lvl) expr
  | Get_tag expr ->
      Fmt.pf ppf "@[<hv>GetTag@;<1 2>@[%a@]@]"
        (pp_expression @@ next_level lvl) expr
  | Get_size expr ->
      Fmt.pf ppf "@[<hv>GetSize@;<1 2>@[%a@]@]"
        (pp_expression @@ next_level lvl) expr
  | Atomic_loc (expr, fld) ->
      Fmt.pf ppf "@[%a@].[%s]"
        (pp_expression lvl) expr
        fld
  | Load (atm, expr1, expr2) ->
      Fmt.pf ppf "@[<hv>GetField %s@;<1 2>@[%a@]@;<1 2>@[%a@]@]"
        (pp_atomicity atm)
        (pp_expression @@ next_level lvl) expr1
        (pp_expression @@ next_level lvl) expr2
  | Store (atm, expr1, expr2, expr3) ->
      Fmt.pf ppf "@[<hv>SetField %s@;<1 2>@[%a@]@;<1 2>@[%a@]@;<1 2>@[%a@]@]"
        (pp_atomicity atm)
        (pp_expression @@ next_level lvl) expr1
        (pp_expression @@ next_level lvl) expr2
        (pp_expression @@ next_level lvl) expr3
  (* When the descriptor is built right here, emit the split-argument wrapper
     of mizzle.stdlib/atomic_loc instead: it names the target as a
     location and a field, so a spec applies to it without the descriptor
     first being reduced to a value. Falls back to the primitive when the
     descriptor arrives as an opaque expression -- an [Atomic.Loc.t] passed
     in, which cannot be split. *)
  | Xchg (Atomic_loc (expr1, fld), expr2) ->
      Fmt.pf ppf "@[<hv>atomic_loc٠xchg@;<1 2>@[%a@]@;<1 2>⟨%s⟩@;<1 2>@[%a@]@]"
        (pp_expression @@ next_level lvl) expr1
        fld
        (pp_expression @@ next_level lvl) expr2
  | Xchg (expr1, expr2) ->
      Fmt.pf ppf "@[<hv>Xchg@;<1 2>@[%a@]@;<1 2>@[%a@]@]"
        (pp_expression @@ next_level lvl) expr1
        (pp_expression @@ next_level lvl) expr2
  | Cas (Atomic_loc (expr1, fld), expr2, expr3) ->
      Fmt.pf ppf "@[<hv>atomic_loc٠cas@;<1 2>@[%a@]@;<1 2>⟨%s⟩@;<1 2>@[%a@]@;<1 2>@[%a@]@]"
        (pp_expression @@ next_level lvl) expr1
        fld
        (pp_expression @@ next_level lvl) expr2
        (pp_expression @@ next_level lvl) expr3
  | Cas (expr1, expr2, expr3) ->
      Fmt.pf ppf "@[<hv>CAS@;<1 2>@[%a@]@;<1 2>@[%a@]@;<1 2>@[%a@]@]"
        (pp_expression @@ next_level lvl) expr1
        (pp_expression @@ next_level lvl) expr2
        (pp_expression @@ next_level lvl) expr3
  | Faa (Atomic_loc (expr1, fld), expr2) ->
      Fmt.pf ppf "@[<hv>atomic_loc٠faa@;<1 2>@[%a@]@;<1 2>⟨%s⟩@;<1 2>@[%a@]@]"
        (pp_expression @@ next_level lvl) expr1
        fld
        (pp_expression @@ next_level lvl) expr2
  | Faa (expr1, expr2) ->
      Fmt.pf ppf "@[<hv>FAA@;<1 2>@[%a@]@;<1 2>@[%a@]@]"
        (pp_expression @@ next_level lvl) expr1
        (pp_expression @@ next_level lvl) expr2
  | Fail ->
      Fmt.pf ppf "Fail"
  | Skip ->
      Fmt.pf ppf "Skip"
and pp_expression lvl ppf expr =
  let lvl_expr = level expr in
  (* [`quot`] and [`rem`] sit at level 35, tighter than [*] at 40, because
     stdpp claims those tokens there and Rocq fixes a notation's level
     globally. Level-driven output is therefore *correct* but misreads: an
     OCaml eye takes [338 * g `quot` 6] for [(338 * g) / 6] when it means
     [338 * (g / 6)]. Parenthesize them always, so the text groups the way it
     parses. *)
  let forced =
    match expr with
    | Binop ((Binop_quot | Binop_rem), _, _) ->
        true
    | _ ->
        false
  in
  if forced || lvl < lvl_expr then
    Fmt.pf ppf "(%a)"
      (pp_expression' lvl_expr) expr
  else
    Fmt.pf ppf "%a"
      (pp_expression' lvl_expr) expr
and pp_expression_if_aux ?(nested = false) ?(force_else = false) ppf expr1 expr2 expr3 =
  Fmt.pf ppf "@[<hv>%sif:@;<1 2>@[%a@]@;then (@]@,  @[%a@]@,)"
    (if nested then " else " else "")
    (pp_expression max_level) expr1
    (pp_expression max_level) expr2 ;
  match expr3 with
  | None ->
      if force_else then
        Fmt.pf ppf " else (@,  ()@,)"
  | Some expr3 ->
      match expr3 with
      | If (expr1, expr2, expr3) ->
          pp_expression_if_aux ~nested:true ppf expr1 expr2 expr3
      | expr ->
          Fmt.pf ppf " else (@,  @[%a@]@,)"
            (pp_expression max_level) expr
and pp_expression_if ?force_else ppf expr1 expr2 expr3 =
  Fmt.pf ppf "@[<v>" ;
  pp_expression_if_aux ?force_else ppf expr1 expr2 expr3 ;
  Fmt.pf ppf "@]"
and pp_branch ppf br =
  Fmt.pf ppf "| " ;
  begin match br.branch_tag with
  | "[]" ->
      Fmt.pf ppf "[]"
  | "::" ->
      let[@warning "-8"] [bdr1; bdr2] = br.branch_fields in
      Fmt.pf ppf "%a :: %a"
        pp_binder bdr1
        pp_binder bdr2
  | _ ->
      Fmt.pf ppf "%s%s%a"
        br.branch_tag
        (match br.branch_fields with [] -> "" | _ -> " ")
        Fmt.(list ~sep:(const char ' ') pp_binder) br.branch_fields
  end ;
  Fmt.pf ppf "%a =>@,    @[%a@]@,"
    Fmt.(option @@ fun ppf -> pf ppf " as %a" pp_local) br.branch_as
    (pp_expression max_level) br.branch_expr
and pp_fallback ppf fb =
  Fmt.pf ppf "|_%a =>@,    @[%a@]@,"
    Fmt.(option @@ fun ppf -> pf ppf " as %a" pp_local) fb.fallback_as
    (pp_expression max_level) fb.fallback_expr
let pp_expression =
  pp_expression max_level

let transl_typ ~lib ~mod_ (global, ty) =
  let spath = String.concat "." [lib; mod_; global] in
  match ty with
  | Type_product flds ->
      flds |> List.mapi @@ fun i fld ->
        Rocq.notation
          LocalityNormal
          fld
          ( fun ppf () ->
              Fmt.pf ppf {|in_type "%s" %i|}
                spath
                i
          )
          "mizzle_proj"
  | Type_record flds ->
      flds |> List.mapi @@ fun i fld ->
        Rocq.notation
          LocalityNormal
          fld
          ( fun ppf () ->
              Fmt.pf ppf {|in_type "%s" %i|}
                spath
                i
          )
          "mizzle_field"
  | Type_variant tags ->
      tags |> List.mapi @@ fun i tag ->
        Rocq.notation
          LocalityNormal
          tag
          ( fun ppf () ->
              Fmt.pf ppf {|in_type "%s" %i|}
                spath
                i
          )
          "mizzle_tag"

let transl_value ~mod_ fresh = function
  | Val_expr (global, expr) ->
      [ Rocq.definition
          LocalityNormal
          Spath.([mod_; global] |> of_list |> to_string)
          (Some "val")
          ( fun ppf () ->
              Fmt.pf ppf "@[%a@]"
                pp_expression expr
          )
      ]
  | Val_fun (global, params, expr) ->
      [ Rocq.definition
          LocalityNormal
          Spath.([mod_; global] |> of_list |> to_string)
          (Some "val")
          ( fun ppf () ->
              Fmt.pf ppf "@[<v>vfun: %a =>@,  @[%a@]@]"
                Fmt.(list ~sep:(const char ' ') pp_binder) params
                pp_expression expr
          )
      ]
  | Val_recs [global, local, params, body] ->
      [ Rocq.definition
          LocalityNormal
          Spath.([mod_; global] |> of_list |> to_string)
          (Some "val")
          ( fun ppf () ->
              Fmt.pf ppf "@[<v>vrec: %a %a =>@,  @[%a@]@]"
                pp_local local
                Fmt.(list ~sep:(const char ' ') pp_binder) params
                pp_expression body
          )
      ]
  | Val_recs recs ->
      let id = fresh () in
      List.concat
      [ [ Rocq.definition
            LocalityLocal
            (Fmt.str "__mizzle_recs_%i" id)
            None
            ( fun ppf () ->
                Fmt.pf ppf "@[<v>( @[<v>recs: %a@]@,)%%mizzle_recs@]"
                  Fmt.(
                    list ~sep:(any "@,and: ") @@ fun ppf (_, local, params, body) ->
                      pf ppf "%a %a =>@,  @[%a@]"
                        pp_local local
                        (list ~sep:(const char ' ') pp_binder) params
                        pp_expression body
                  ) recs
            )
        ]
      ; List.mapi (fun i (global, _, _, _) ->
          Rocq.definition
            LocalityNormal
            Spath.([mod_; global] |> of_list |> to_string)
            None
            ( fun ppf () ->
                Fmt.pf ppf "ValRecs %i __mizzle_recs_%i"
                  i
                  id
            )
        ) recs
      ; List.mapi (fun i (global, _, _, _) ->
          Rocq.instance
            LocalityGlobal
            None
            ( fun ppf () ->
                Fmt.pf ppf "@[<v>AsValRecs' %a %i __mizzle_recs_%i [@,  @[<v>%a@]@,]@]"
                  Spath.pp Spath.([mod_; global] |> of_list)
                  i
                  id
                  Fmt.(
                    list ~sep:(any " ;@,") @@ fun ppf (global, _, _, _) ->
                      Spath.([mod_; global] |> of_list |> pp ppf)
                  ) recs
            )
        ) recs
      ]
  | Val_opaque global ->
      [ Rocq.parameter
          Spath.([mod_; global] |> of_list |> to_string)
          "val"
      ]
let transl_value ~mod_ =
  let gen = ref 0 in
  transl_value ~mod_ (fun () -> let i = !gen in gen := i + 1 ; i)

let transl ~code t =
  let rocq =
    if code then
      List.map (transl_value ~mod_:t.module_) (values t)
    else
      List.map (transl_typ ~lib:t.library ~mod_:t.module_) (types t)
  in
  let rocq = List.interleave [Rocq.newline] rocq in
  (* Requires are emitted against Mizzle's vendored language rather than the
     [zoo] theory; [Mizzle.require] holds the mapping. [options] stays last,
     because a require block that also pulls in stdpp must import it last or
     stdpp's tactics shadow Mizzle's. *)
  let require lib mods =
    (* [zoo.language]'s [typeclasses] and [notations] both map onto Mizzle's
       [instances], so the mapped module list needs deduplicating. *)
    let dedup mods =
      List.fold_left (fun acc mod_ ->
        if List.mem mod_ acc then acc else mod_ :: acc
      ) [] mods |> List.rev
    in
    (* One require per distinct target path, in first-seen order: a single
       source library may well straddle two Mizzle theories. *)
    let mapped = List.filter_map (Mizzle.require lib) mods in
    let paths = dedup @@ List.map fst mapped in
    List.map (fun path ->
      Rocq.require RequireImport path
        (dedup @@ List.filter_map (fun (path', mod_) ->
          if path' = path then Some mod_ else None
        ) mapped)
    ) paths
  in
  List.concat (
    [ require "zoo" ["prelude"]
    ; require "zoo.language" ["typeclasses"; "notations"]
    ; List.concat @@ Hashtbl.map_list (fun lib mods ->
        require lib (List.rev @@ Hashset.to_list mods)
      ) t.dependencies
    ; if code && !Mizzle.types then
        require t.library [t.module_ ^ "__types"]
      else
        []
    ; require "zoo" ["options"]
    ; [ Rocq.newline
      ]
    ] @
    rocq
  )
let transl_types =
  transl ~code:false
let transl_code =
  transl ~code:true
