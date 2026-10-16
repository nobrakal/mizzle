type module_ =
  { module_name: string
  ; module_impl: string
  ; module_cmt: string
  ; module_cmti: string option
  }

type library =
  { library_name: string
  ; library_local: bool
  ; library_modules: (string, module_) Hashtbl.t
  }

type t =
  { build_context: string
  ; libraries: (string, library) Hashtbl.t
  }

val of_directory :
  unit -> (t, string) Result.t

val pp :
  t Fmt.t
