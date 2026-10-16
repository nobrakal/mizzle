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

val newline :
  item
val require :
  require_kind -> path -> path list -> item
val parameter :
  ident -> term -> item
val definition :
  locality -> ident -> term option -> custom -> item
val instance :
  locality -> ident option -> custom -> item
val notation :
  locality -> string -> custom -> scope -> item
val opaque :
  locality -> ident -> item

type t =
  item list

val pp :
  t Fmt.t
