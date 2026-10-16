let transl (t : Interface.t) =
  List.concat
  [ ( match Mizzle.require t.library (t.module_ ^ "__code") with
      | None ->
          [ Rocq.newline ]
      | Some (path, mod_) ->
          [ Rocq.require RequireImport path [mod_]
          ; Rocq.newline
          ]
    )
  ; List.map (fun global ->
      Rocq.opaque LocalityGlobal Spath.([t.module_; global] |> of_list |> to_string)
    ) t.values
  ]
