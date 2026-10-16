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

val main :
  arguments -> unit
