type path =
  string

type ident =
  string

type term =
  string

type scope =
  string

type require_kind =
  | RequireOnly
  | RequireImport
  | RequireExport

type locality =
  | LocalityNormal
  | LocalityLocal
  | LocalityGlobal

type custom =
  unit Fmt.t

type item =
  | Newline
  | Require of require_kind * path * path list
  | Parameter of ident * term
  | Definition of locality * ident * term option * custom
  | Instance of locality * ident option * custom
  | Notation of locality * string * custom * scope
  | Opaque of locality * ident

type t =
  item list

let newline =
  Newline
let[@inline] require kind path paths =
  Require (kind, path, paths)
let[@inline] parameter id tm =
  Parameter (id, tm)
let[@inline] definition local id tm custom =
  Definition (local, id, tm, custom)
let[@inline] instance local id custom =
  Instance (local, id, custom)
let[@inline] notation local str custom scope =
  Notation (local, str, custom, scope)
let[@inline] opaque local id =
  Opaque (local, id)

let pp_require_kind ppf = function
  | RequireOnly ->
      ()
  | RequireImport ->
      Fmt.pf ppf " Import"
  | RequireExport ->
      Fmt.pf ppf " Export"

let pp_locality ppf = function
  | LocalityNormal ->
      ()
  | LocalityLocal ->
      Fmt.pf ppf "#[local] "
  | LocalityGlobal ->
      Fmt.pf ppf "#[global] "

let pp_item ppf = function
  | Newline ->
      ()
  | Require (kind, path, paths) ->
      if not @@ List.is_empty paths then
        Fmt.pf ppf "From %s Require%a@,  %a."
          path
          pp_require_kind kind
          Fmt.(list ~sep:(any "@,  ") string) paths
  | Parameter (id, tm) ->
      Fmt.pf ppf "Parameter %s : %s."
        id
        tm
  | Definition (local, id, tm, custom) ->
      Fmt.pf ppf "%aDefinition %s%a :=@,  %a."
        pp_locality local
        id
        Fmt.(option @@ fmt " : %s") tm
        custom ()
  | Instance (local, id, custom) ->
      Fmt.pf ppf "%aInstance %a:@,  %a.@,Proof.@,  done.@,Qed."
        pp_locality local
        Fmt.(option string) id
        custom ()
  | Notation (local, str, custom, scope) ->
      Fmt.pf ppf {|%aNotation "'%s'" := (@,  %a@,)(in custom %s@,).|}
        pp_locality local
        str
        custom ()
        scope
  | Opaque (local, id) ->
      Fmt.pf ppf "%aOpaque %s."
        pp_locality local
        id

let pp ppf t =
  Fmt.pf ppf "@[<v>" ;
  Fmt.list pp_item ppf t ;
  Fmt.pf ppf "@]"
