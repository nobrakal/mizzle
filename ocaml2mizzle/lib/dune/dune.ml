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

type sexp = Csexp.t =
  | Atom of string
  | List of sexp list

exception Of_sexp of string
let[@inline] invalid () =
  raise @@ Of_sexp "dune description is ill-formed"
let (let@) sexp fn =
  match sexp with
  | Atom _ ->
      invalid ()
  | List sexps ->
      fn sexps
let (let<) sexps fn =
  match sexps with
  | [] ->
      invalid ()
  | sexp :: _ ->
      fn sexp
let (let<@) sexps fn =
  match sexps with
  | List sexps :: _ ->
      fn sexps
  | _ ->
      invalid ()
let rec bool_of_sexp = function
  | Atom "true" ->
      true
  | Atom "false" ->
      false
  | List [sexp] ->
      bool_of_sexp sexp
  | _ ->
      invalid ()
let rec string_of_sexp = function
  | Atom str ->
      str
  | List [sexp] ->
      string_of_sexp sexp
  | _ ->
      invalid ()
let module_of_sexp sexp =
  let@ sexps = sexp in
  let name = ref "" in
  let impl = ref "" in
  let cmt = ref "" in
  let cmti = ref None in
  List.iter (function
    | List (Atom "name" :: sexps) ->
        let< sexp = sexps in
        name := string_of_sexp sexp
    | List (Atom "impl" :: sexps) ->
        let<@ sexps = sexps in
        let< sexp = sexps in
        impl := string_of_sexp sexp
    | List (Atom "cmt" :: sexps) ->
        let< sexp = sexps in
        cmt := string_of_sexp sexp
    | List (Atom "cmti" :: sexps) ->
        let< sexp = sexps in
        if sexp <> List [] then
          cmti := Some (string_of_sexp sexp)
    | _ ->
        ()
  ) sexps ;
  let name = if !name = "" then invalid () ; !name in
  let name = String.uncapitalize_ascii name in
  let impl = if !impl = "" then invalid () ; !impl in
  let cmt = if !cmt = "" then invalid () ; !cmt in
  let cmti = !cmti in
  { module_name= name
  ; module_impl= impl
  ; module_cmt= cmt
  ; module_cmti= cmti
  }
let library_of_sexp sexp =
  let@ sexps = sexp in
  let name = ref "" in
  let local = ref None in
  let mods = Hashtbl.create () in
  List.iter (function
    | List (Atom "name" :: sexps) ->
        let< sexp = sexps in
        name := String.uncapitalize_ascii (string_of_sexp sexp)
    | List (Atom "local" :: sexps) ->
        let< sexp = sexps in
        local := Some (bool_of_sexp sexp)
    | List (Atom "modules" :: sexps) ->
        let<@ sexps = sexps in
        List.iter (fun sexp ->
          let mod_ = module_of_sexp sexp in
          Hashtbl.add mods mod_.module_name mod_
        ) sexps
    | _ ->
        ()
  ) sexps ;
  let name = if !name = "" then invalid () ; !name in
  let local = Option.get_lazy invalid !local in
  { library_name= name
  ; library_local= local
  ; library_modules= mods
  }
let of_sexp sexp =
  let@ sexps = sexp in
  let ctx = ref "" in
  let libs = Hashtbl.create () in
  List.iter (function
    | List (Atom "build_context" :: sexps) ->
        let< sexp = sexps in
        ctx := string_of_sexp sexp
    | List (Atom "library" :: sexps) ->
        let< sexp = sexps in
        let lib = library_of_sexp sexp in
        Hashtbl.add libs lib.library_name lib
    | _ ->
        ()
  ) sexps ;
  let ctx = if !ctx = "" then invalid () ; !ctx in
  { build_context= ctx
  ; libraries= libs
  }
let of_sexp sexp =
  try
    Ok (of_sexp sexp)
  with Of_sexp err ->
    Error err

let describe_command =
  "dune describe --lang 0.1 --format csexp --root ."
let of_directory () =
  let chan = Unix.open_process_in describe_command in
  set_binary_mode_in chan false ;
  Fun.protect ~finally:(fun () -> close_in chan) @@ fun () ->
    Result.bind (Csexp.input chan) of_sexp

let pp_module ppf mod_ =
  Fmt.pf ppf "+ %s@,  @[<v>+ impl: %s@,+ cmt: %s@,+ cmti: %s@]"
    mod_.module_name
    mod_.module_impl
    mod_.module_cmt
    (Option.value ~default:"∅" mod_.module_cmti)
let pp_library ppf lib =
  Fmt.pf ppf "+ %s (%s)@,  @[<v>%a@]"
    lib.library_name
    (if lib.library_local then "local" else "extern")
    (Fmt.hashtbl @@ fun ppf (_, mod_) -> pp_module ppf mod_) lib.library_modules
let pp ppf t =
  Fmt.pf ppf "@[<v>%a@]"
    (Fmt.hashtbl @@ fun ppf (_, lib) -> pp_library ppf lib) t.libraries
