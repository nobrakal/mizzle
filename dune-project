(lang dune 3.23)
(using rocq 0.13)

(name mizzle)

(generate_opam_files)

(license MIT)

(authors
  "Alexandre Moine"
  "Sam Westrick"
  "Joseph Tassarotti"
)
(maintainers
  "Alexandre Moine <alexandre.moine@inria.fr>"
)

(package
  (name mizzle)
  (synopsis "Mizzle")
  (depends
    (ocaml (= 5.4.1))
    ; Pinned to the versions the development is checked against: iris-dev
    ; publishes new snapshots continuously, and the latest is not guaranteed
    ; to build.
    (rocq-core (= 9.1.1))
    (rocq-stdlib (= 9.2.0))
    (rocq-equations (= 1.3.1+9.1))
    (rocq-stdpp (= dev.2026-01-28.0.6f3f2617))
    (rocq-iris (= dev.2026-02-05.0.9815f03b))
    coq-lsp
    domainslib
    ; ocaml2mizzle/ is vendored in-tree; these are its own dependencies.
    ocaml-compiler-libs
    csexp
    fmt
    cmdliner
  )
  (allow_empty)
)
