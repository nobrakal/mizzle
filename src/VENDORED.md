# Code vendored from Zoo

MizzleLang, the language Mizzle reasons about, is not original work. It is a
modified copy of ZooLang, the language of the Zoo project, and most of
`lang/` and the program text in `stdlib/` are copied from Zoo.

- Upstream: <https://github.com/clef-men/zoo>, by Clément Allain.
- Copied from upstream commit `b35e0b7210340f887447e78d28648bdda2858804`
  (2026-05-14), the version Mizzle depended on through opam before vendoring.
- License: ISC, reproduced at the end of this file.

The OCaml-to-Rocq translator is vendored separately, as `ocaml2mizzle/`. See
`ocaml2mizzle/VENDORED.md`.

## What comes from Zoo

Each file states its origin in its header comment, naming the upstream file(s)
it was copied from and how it departs from them.

| here                         | upstream (under `theories/`)                                   |
|------------------------------|----------------------------------------------------------------|
| `lang/syntax.v`              | `zoo/language/` (forked)                                       |
| `lang/semantics.v`           | `zoo/language/` (forked)                                       |
| `lang/instances.v`           | `zoo/language/tactics.v`, `zoo/language/typeclasses.v`         |
| `lang/classes.v`             | `zoo/common/{typeclasses,string,binder,math}.v`                |
| `lang/list.v`                | `zoo/common/list.v`                                            |
| `lang/prelude.v`             | `zoo/prelude.v`                                                |
| `lang/options.v`             | `zoo/tactics.v`, `zoo/options.v`                               |
| `lib/big_sepL.v`             | `zoo/iris/bi/big_op/big_sepL.v`                                |
| `stdlib/array.v`, `condition.v`, `domain.v`, `dynarray_1.v`, `ivar_2.v`, `mutex.v` | `zoo_std/*__code.v` (program text only) |
| `stdlib/assert.v`, `assume.v` | `zoo_std/{assert,diverge,assume}.v` (program text only)       |
| `stdlib/structural_equality.v` | `zoo/program_logic/structural_equality.v`                    |

The copies are restricted to what Mizzle uses. In `stdlib/`, only the program
text is Zoo's: the specifications are Mizzle's goal-mode specs, which replace
Zoo's WP specs. Everything else under `src/` is Mizzle's own, including
`lang/alt_semantics.v` (bound-checked semantics and its correspondence to the
copied one), `lang/block_heap_complete_preserved.v`, `lang/locs_in_headers.v`,
`stdlib/atomic_loc.v`, `stdlib/rand.v`, `stdlib/structeq.v` and
`stdlib/trace.v` (a port of Iris's `heap_lang.lib.trace`).

## Departures from ZooLang

The main ones, detailed in the file headers:

- field accesses carry an `atomicity` flag (`syntax.v`), which does not affect
  steps (`semantics.v`);
- `Emit` records an observation and replaces prophecies (`Proph`, `Resolve`);
- no strings or chars;
- the semantics is Mizzle's own `prim_step` / `nsteps`, not an instance of
  Iris's `language`; evaluation stays right-to-left, as in Zoo.

## Renaming

Identifiers that Zoo prefixes with `zoo` are renamed with a `mizzle` prefix,
with no other change:

| Zoo                                     | MizzleLang                                    |
|-----------------------------------------|-----------------------------------------------|
| custom entries `zoo_tag`, `zoo_proj`, `zoo_field`, `zoo_branch`, `zoo_rec` | `mizzle_tag`, `mizzle_proj`, `mizzle_field`, `mizzle_branch`, `mizzle_rec` |
| scope `zoo_recs_scope`, `__zoo_recs*`   | `mizzle_recs_scope`, `__mizzle_recs*`         |
| tactics `zoo_simplify`, `zoo_simpl`, `zoo_fold_typeclasses` | `mizzle_simplify`, `mizzle_simpl`, `mizzle_fold_typeclasses` |
| hint database `zoo`                     | `mizzle`                                      |

Strings naming upstream OCaml types, such as `in_type "zoo_std.ivar_2.t"`, are
left unchanged.

## License of the copied code

```
Copyright (c) 2024, Clément Allain <clement.allain@inria.fr>

Permission to use, copy, modify, and/or distribute this software for any
purpose with or without fee is hereby granted, provided that the above
copyright notice and this permission notice appear in all copies.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
```
