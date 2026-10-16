type arguments =
  { input: string
  ; output: string
  ; force: bool
  ; quiet: bool
  ; ignore: string list
  ; only: string list
  ; describe: bool
  }

exception Error of unit Cmdliner.Term.ret

let error ?(usage = true) fmt =
  Fmt.kstr (fun msg ->
    raise @@ Error (`Error (usage, msg))
  ) ("@[<v>" ^^ fmt ^^ "@]")
let invalid_cmt ?(usage = true) fmt =
  error ~usage ("invalid .cmt file" ^^ fmt)
let invalid_cmti ?(usage = true) fmt =
  error ~usage ("invalid .cmti file" ^^ fmt)
let invalid_directory ?(usage = true) fmt =
  error ~usage ("invalid directory" ^^ fmt)

type output =
  { output_types: string
  ; output_code: string
  ; output_opaque: string
  }
let output output_dir mod_name =
  let output = Filename.concat output_dir mod_name in
  { output_types= output ^ "__types.v"
  ; output_code= output ^ "__code.v"
  ; output_opaque= output ^ "__opaque.v"
  }

let implementation ~lib_name ~mod_name ~input ~output =
  match Cmt_format.read_cmt input with
  | exception Sys_error err ->
      invalid_cmt ": %s" err
  | exception Cmt_format.Error _
  | exception Cmi_format.Error _ ->
      invalid_cmt ""
  | cmt ->
      match cmt.cmt_annots with
      | Implementation str ->
          Load_path.(init ~auto_include:no_auto_include ~visible:cmt.cmt_loadpath.visible ~hidden:cmt.cmt_loadpath.hidden) ;
          begin match Mizzlelang.Implementation_of_cmt.transl_structure ~lib:lib_name ~mod_:mod_name str with
          | exception Mizzlelang.Implementation_of_cmt.Error (loc, err) ->
              error ~usage:false "%a:@,%a"
                Location.print_loc loc
                Mizzlelang.Implementation_of_cmt.Error.pp err
          | exception Mizzlelang.Implementation_of_cmt.Ignore ->
              ()
          | impl ->
              if !Mizzlelang.Mizzle.types then (
                let rocq = Mizzlelang.Implementation_to_rocq.transl_types impl in
                Out_channel.with_open_text output.output_types (fun chan ->
                  Fmt.pf (Format.formatter_of_out_channel chan) "%a@." Mizzlelang.Rocq.pp rocq
                )
              ) ;
              let rocq = Mizzlelang.Implementation_to_rocq.transl_code impl in
              Out_channel.with_open_text output.output_code (fun chan ->
                Fmt.pf (Format.formatter_of_out_channel chan) "%a@." Mizzlelang.Rocq.pp rocq
              )
          end
      | _ ->
          invalid_cmt ": not an implementation"

let interface ~lib_name ~mod_name ~input ~output =
  match Cmt_format.read_cmt input with
  | exception Sys_error err ->
      invalid_cmti ": %s" err
  | exception Cmt_format.Error _
  | exception Cmi_format.Error _ ->
      invalid_cmti ""
  | cmt ->
      match cmt.cmt_annots with
      | Interface sig_ ->
          Load_path.(init ~auto_include:no_auto_include ~visible:cmt.cmt_loadpath.visible ~hidden:cmt.cmt_loadpath.hidden) ;
          begin match Mizzlelang.Interface_of_cmti.transl_signature ~lib:lib_name ~mod_:mod_name sig_ with
          | exception Mizzlelang.Interface_of_cmti.Ignore ->
              ()
          | intf ->
              let rocq = Mizzlelang.Interface_to_rocq.transl intf in
              Out_channel.with_open_text output.output_opaque (fun chan ->
                Fmt.pf (Format.formatter_of_out_channel chan) "%a@." Mizzlelang.Rocq.pp rocq
              )
          end
      | _ ->
          invalid_cmti ": not an interface"

let main_singlefile args =
  let input = args.input in
  let lib_name = Filename.(input |> dirname |> basename) |> String.uncapitalize_ascii in
  let mod_name = Filename.(input |> basename |> remove_extension) |> String.uncapitalize_ascii in
  let output = output args.output mod_name in
  implementation ~lib_name ~mod_name ~input ~output

let check ~args ~input ~output =
  if args.force then
    true
  else
    match Unix.stat input with
    | exception Unix.Unix_error _ ->
        invalid_cmt ""
    | input_stats ->
        match Unix.stat output.output_code with
        | output_stats when input_stats.st_mtime < output_stats.st_mtime ->
            false
        | _
        | exception Unix.Unix_error _ ->
            true
let main_directory args (dune : Dune.t) =
  let ignore = List.map String.uncapitalize_ascii args.ignore in
  let only = List.map String.uncapitalize_ascii args.only in
  dune.libraries |> Hashtbl.iter @@ fun _ (lib : Dune.library) ->
    if lib.library_local then
      let lib_name = lib.library_name in
      if not (List.mem lib_name ignore) && (only = [] || List.mem lib_name only) then
        let output_dir = Filename.concat args.output lib_name in
        begin try Sys.mkdir output_dir 0o777 with Sys_error _ -> () end ;
        lib.library_modules |> Hashtbl.iter @@ fun mod_name (mod_ : Dune.module_) ->
          if not @@ Filename.check_suffix mod_.module_impl "-gen" then
            let input = Filename.concat args.input mod_.module_cmt in
            let output = output output_dir mod_name in
            if check ~args ~input ~output then (
              implementation ~lib_name ~mod_name ~input ~output ;
              match mod_.module_cmti with
              | None ->
                  ()
              | Some cmti ->
                  let input = Filename.concat args.input cmti in
                  interface ~lib_name ~mod_name ~input ~output
            ) else if not args.quiet then
              Fmt.pr {|Ignoring module "%s" from library "%s" (already up-to-date).@.|}
                mod_name
                lib_name
let main_directory args =
  begin try
    Sys.chdir args.input
  with Sys_error _ ->
    error "cannot move to input directory"
  end ;
  match Dune.of_directory () with
  | Error err ->
      error "%s" err
  | Ok dune ->
      if args.describe then
        Fmt.pr "%a@." Dune.pp dune
      else (
        begin try
          Sys.chdir dune.build_context
        with Sys_error _ ->
          error "cannot move to %s" (Filename.concat args.input dune.build_context)
        end ;
        main_directory args dune
      )

let main args =
  let input =
    try
      Unix.realpath args.input
    with Unix.Unix_error _ ->
      error "invalid input file"
  in
  let output =
    try
      Unix.realpath args.output
    with Unix.Unix_error _ ->
      error "invalid output directory"
  in
  let args = { args with input; output } in
  if Filename.extension args.input = ".cmt" then
    main_singlefile args
  else if Sys.is_directory args.input then
    main_directory args
  else
    invalid_directory ""
