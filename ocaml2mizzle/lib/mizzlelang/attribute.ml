type t =
  Parsetree.attribute

let has attr =
  List.exists (fun attr' -> attr'.Parsetree.attr_name.txt = attr)

let mizzle =
  "mizzle"
let has_mizzle =
  has mizzle

let ignore =
  mizzle ^ ".ignore"
let has_ignore =
  has ignore

let force_record =
  mizzle ^ ".force_record"
let has_force_record =
  has force_record

let reveal =
  mizzle ^ ".reveal"
let has_reveal =
  has reveal

let opaque =
  mizzle ^ ".opaque"
let has_opaque =
  has opaque

type overwrite_kind =
  | Overwrite of Asttypes.rec_flag
  | Raw
let overwrite_kind_to_string = function
  | Raw ->
      "_raw"
  | Overwrite rec_ ->
      match rec_ with
      | Nonrecursive ->
          ""
      | Recursive ->
          "_rec"
let overwrite =
  mizzle ^ ".overwrite"
let rec has_overwrite = function
  | [] ->
      None
  | attr :: attrs ->
      let attr_name = attr.Parsetree.attr_name.txt in
      if String.starts_with ~prefix:overwrite attr_name then
        let overwrite_len = String.length overwrite in
        let attr_len = String.length attr_name in
        match String.sub attr_name overwrite_len (attr_len - overwrite_len) with
        | "" ->
            Some (Overwrite Nonrecursive, attr)
        | "_rec" ->
            Some (Overwrite Recursive, attr)
        | "_raw" ->
            Some (Raw, attr)
        | _ ->
            has_overwrite attrs
      else
        has_overwrite attrs
