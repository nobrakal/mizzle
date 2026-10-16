open Interface

exception Ignore

let transl_signature_item (sig_item : Typedtree.signature_item) =
  match sig_item.sig_desc with
  | Tsig_value val_descr ->
      Some (Ident.name val_descr.val_id)
  | Tsig_attribute attr ->
      if Attribute.has_ignore [attr] then
        raise Ignore ;
      None
  | _ ->
      None

let transl_signature ~lib ~mod_ (sig_ : Typedtree.signature) =
  let values = List.filter_map transl_signature_item sig_.sig_items in
  { library= lib
  ; module_= mod_
  ; values
  }
