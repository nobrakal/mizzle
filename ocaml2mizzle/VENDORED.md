# Vendored copy of `ocaml2zoo`

`ocaml2mizzle` is a vendored and modified copy of `ocaml2zoo`, the
OCaml-to-Rocq AST translator of the Zoo project. Almost all of its code is
upstream's; the changes listed below adapt it to Mizzle's language
(MizzleLang) and to released OCaml.

- Upstream: <https://github.com/clef-men/ocaml2zoo>, by Clément Allain.
- Forked from upstream commit `b8957fa340b56d5fd9802403d263cdd002135199`
  (2026-04-27, "zoo: Introduce [Name] and [Spath].").
- License: ISC, reproduced in `LICENSE.md`. The copyright notice there is
  upstream's and must be kept.

It used to be an opam dependency; it lives in-tree so that the generator and
the language it targets can evolve together.

## Renaming

The tool is renamed from `ocaml2zoo` to `ocaml2mizzle`, because it now emits
MizzleLang rather than Zoo. The renaming is purely mechanical:

| upstream                          | here                                      |
|-----------------------------------|-------------------------------------------|
| directory `ocaml2zoo/`            | `ocaml2mizzle/`                           |
| package, binary `ocaml2zoo`       | `ocaml2mizzle`                            |
| `bin/ocaml2zoo.ml`                | `bin/ocaml2mizzle.ml`                     |
| library `ocaml2zoo.base`          | `ocaml2mizzle.base`                       |
| library `zoo` (`lib/zoo/`)        | `mizzlelang` (`lib/mizzlelang/`)          |
| attributes `[@zoo.*]`             | `[@mizzle.*]` (`attribute.ml`)            |
| ignore file `.zooignore`          | `.mizzleignore`                           |
| emitted `zoo_tag`, `zoo_proj`, `zoo_field`, `zoo_branch`, `__zoo_recs`, scope `%zoo_recs` | `mizzle_*`, `__mizzle_recs`, `%mizzle_recs` |
| description "OCaml to Zoo"       | "OCaml to MizzleLang"                     |
| tests `tests/zoo_*.ml`            | `tests/mizzle_*.ml`                       |

Some internal names still mention Zoo on purpose: the library keys `"zoo"`,
`"zoo.language"` and `"zoo_std"` (`implementation_of_cmt.ml`,
`implementation_to_rocq.ml`, `mizzlelang/mizzle.ml`) name upstream's Rocq
theories, which `Mizzle.require` translates to `mizzle.lang` /
`mizzle.stdlib`. The opam metadata (`dune-project`) lists upstream's author
first, and names Mizzle's repository as the source and Mizzle's maintainer
as maintainer. `README.md` is upstream's, with a note added at the top.

## Local patches

Apart from the renaming, the copy carries these changes.

**Port to released OCaml 5.4.1.** Upstream targets a patched compiler that
supports
[generative constructors](https://github.com/clef-men/ocaml/tree/generative_constructors),
which 5.4.1 does not have, so the port drops that support and the two test
cases exercising it. The enclosing `theories/dune-project` pins
`(ocaml (= 5.4.1))`, so re-syncing with upstream means rebasing this port, not
taking upstream verbatim.

**`while` loops.** Backported from upstream commit `95530ac` ("lib/zoo:
Support while loops."), adapted to Mizzle's notations
(`while: e0 begin e1 end`) and without the `zoo.program_logic.while_`
dependency, since `While` is a constructor of MizzleLang proper.

**Retargeting at MizzleLang.**

- `lib/mizzlelang/mizzle.ml{,i}` (new) map OCaml library names onto Rocq
  logical paths under `mizzle.lang` / `mizzle.stdlib`, and
  `implementation_to_rocq.ml` / `interface_to_rocq.ml` emit their requires
  through `Mizzle.require`;
- `bin/ocaml2mizzle.ml` gains the `--rocq-prefix`, `--rocq-lib` and
  `--no-types` options steering that mapping;
- field accesses carry an explicit atomicity flag (`implementation.ml`,
  `implementation_to_rocq.ml`);
- `Atomic.compare_and_set` / `exchange` / `fetch_and_add` on a descriptor built
  at the call site emit the split-argument `atomic_loc٠*` wrappers of
  `mizzle.stdlib.atomic_loc` (`implementation_of_cmt.ml`,
  `implementation_to_rocq.ml`);
- top-level values print with Mizzle's `vfun:` / `vrec:` notations, and the
  `tests/*.exp` expectations are re-promoted accordingly.

To see the full divergence, check out upstream at the commit above, apply the
renaming table, and diff against this directory. Record any further
Mizzle-specific change here, or the next sync will be guesswork.

## Building

The build is wired into the enclosing dune workspace: `ocaml2mizzle/` is a
nested dune project (like `dataracebench/` and `linearizable/`), so
`dune build` at `theories/` builds the translator too, and `gen_mizzle.sh` runs
the freshly built binary out of `_build/` rather than whatever happens to be on
`PATH`. Its OCaml dependencies (`ocaml-compiler-libs`, `csexp`, `fmt`,
`cmdliner`) are listed in `theories/dune-project`, which `setup.sh` installs.

The upstream `Makefile` and `tests/run.sh` still work standalone, from within
this directory.
