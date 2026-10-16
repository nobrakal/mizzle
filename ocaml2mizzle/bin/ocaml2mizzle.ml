open Cmdliner

let input =
  let docv = "input" in
  let doc = "Input dune project or .cmt file." in
  Arg.(required & pos 0 (some file) None & info [] ~docv ~doc)

let output =
  let docv = "output" in
  let doc = "Output directory." in
  Arg.(required & pos 1 (some dir) None & info [] ~docv ~doc)

let force =
  let doc = "Force generation for up-to-date targets." in
  Arg.(value & flag & info ["f";"force"] ~doc)

let quiet =
  let doc = "Enable quiet mode." in
  Arg.(value & flag & info ["q";"quiet"] ~doc)

let ignore_file =
  ".mizzleignore"
let ignore =
  let docv = "library" in
  let doc = "Prevent a library from being processed." in
  Arg.(value & opt_all string [] & info ["ignore"] ~docv ~doc)

let only =
  let docv = "library" in
  let doc = "Mark a library. Only marked libraries are processed." in
  Arg.(value & opt_all string [] & info ["only"] ~docv ~doc)

let describe =
  let doc = "Only dump description of dune project." in
  Arg.(value & flag & info ["describe"] ~doc)

(* Mizzle-specific: see lib/mizzlelang/mizzle.mli. These replace the post-processing
   pass that gen_mizzle.sh used to run over the generated files. *)
let rocq_prefix =
  let docv = "path" in
  let doc =
    "Rocq logical path prefixing the project's own libraries, so that a dune \
     library $(i,l) is required as $(i,path).$(i,l)."
  in
  Arg.(value & opt string "" & info ["rocq-prefix"] ~docv ~doc)

let rocq_lib =
  let docv = "library=target" in
  let doc =
    "Rewrite requires of $(i,library). $(i,target) is empty to drop the \
     require, $(i,path) to rewrite the library, or $(i,path):$(i,module) to \
     also collapse its modules to $(i,module). Repeatable."
  in
  Arg.(value & opt_all string [] & info ["rocq-lib"] ~docv ~doc)

let no_types =
  let doc = "Do not generate (nor require) the __types files." in
  Arg.(value & flag & info ["no-types"] ~doc)

let info =
  let doc = "OCaml to MizzleLang" in
  Cmd.info "ocaml2mizzle" ~doc

let main
  input
  output
  force
  quiet
  ignore
  only
  describe
  rocq_prefix
  rocq_lib
  no_types
=
  let ignore =
    try
      In_channel.with_open_text ignore_file (fun input ->
        In_channel.fold_lines (fun ignore line ->
          String.trim line :: ignore
        ) ignore input
      )
    with Sys_error _ ->
      ignore
  in
  let args : Main.arguments =
    { input
    ; output
    ; force
    ; quiet
    ; ignore
    ; only
    ; describe
    }
  in
  try
    Mizzlelang.Mizzle.set_prefix rocq_prefix ;
    Mizzlelang.Mizzle.types := not no_types ;
    List.iter (fun str ->
      match Mizzlelang.Mizzle.parse_override str with
      | Either.Left (lib, target) ->
          Mizzlelang.Mizzle.add_override lib target
      | Either.Right err ->
          raise @@ Main.Error (`Error (true, Fmt.str "invalid --rocq-lib: %s" err))
    ) rocq_lib ;
    `Ok (Main.main args)
  with Main.Error err -> err
let main =
  let open Term in
  ret (
    const main
    $ input
    $ output
    $ force
    $ quiet
    $ ignore
    $ only
    $ describe
    $ rocq_prefix
    $ rocq_lib
    $ no_types
  )
let () =
  Cmd.v info main
  |> Cmd.eval
  |> exit
