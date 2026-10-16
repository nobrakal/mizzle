let test1 =
  object end
[@@mizzle.overwrite
  fun () -> ()
]

let test2 =
  object end
[@@mizzle.overwrite_rec
  fun () -> test2 ()
]

let test3 =
  object end
[@@mizzle.overwrite_raw "foo.bar.raw"]

let test4 () =
  object end
[@@mizzle.overwrite_raw "foo.bar.raw"]
