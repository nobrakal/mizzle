let lang =
  "mizzle.lang"
let stdlib =
  "mizzle.stdlib"

type target =
  | Rename of string
  | Rename_module of string * string
  | Drop

let types =
  ref true

let prefix =
  ref ""
let set_prefix path =
  prefix := path

let overrides =
  ref []
let add_override lib target =
  overrides := (lib, target) :: !overrides

let parse_override str =
  match String.index_opt str '=' with
  | None ->
      Either.Right (Fmt.str "expected <library>=<target>, got %S" str)
  | Some i ->
      let lib = String.sub str 0 i in
      let spec = String.sub str (i + 1) (String.length str - i - 1) in
      if lib = "" then
        Either.Right (Fmt.str "empty library name in %S" str)
      else
        Either.Left ( lib
                    , if spec = "" then
                        Drop
                      else
                        match String.index_opt spec ':' with
                        | None ->
                            Rename spec
                        | Some j ->
                            Rename_module
                              ( String.sub spec 0 j
                              , String.sub spec (j + 1) (String.length spec - j - 1)
                              )
                    )

(* The [zoo] theory's modules, as Mizzle vendored them: the language proper
   went to [mizzle.lang], the program text of the standard library to
   [mizzle.stdlib]. *)
let of_zoo mod_ =
  match mod_ with
  | "structural_equality" ->
      Some (stdlib, mod_)
  | _ ->
      Some (lang, mod_)

let require lib mod_ =
  match List.assoc_opt lib !overrides with
  | Some Drop ->
      None
  | Some (Rename path) ->
      Some (path, mod_)
  | Some (Rename_module (path, mod_')) ->
      Some (path, mod_')
  | None ->
      match lib with
      | "zoo" ->
          of_zoo mod_
      | "zoo.language" ->
          (* Mizzle's [instances] re-exports the syntax and the notations, so
             it stands in for [typeclasses] + [notations]. *)
          Some (lang, "instances")
      | "zoo_std" | "stdlib" when mod_ = "stdlib" ->
          (* A reference to an OCaml [Stdlib] value with no Zoo counterpart
             yields a self-named dependency; there is nothing to require. *)
          None
      | "zoo_std" | "stdlib" ->
          (* Mizzle keeps each primitive's program text and goal-mode specs
             in one file, named after the Zoo module. *)
          Some (stdlib, mod_)
      | _ ->
          if !prefix = "" then
            Some (lib, mod_)
          else
            Some (!prefix ^ "." ^ lib, mod_)
