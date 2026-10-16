## Rocq theories

Run `./setup.sh` to set-up OCaml/Rocq dependencies.

It will create a local opam switch
with correct dependencies, and build the project.
Please allow at least 30 minutes for
the installation and build to run.

If you run into troubles, see `mizzle.opam` for the
exact list of dependencies.

### rocq-mcp

We're going to install rocq-mcp (a python library) in
a virtual env (I'm following the OPAM philosophy to
have dependencies in the same project directory).

You need to first install [uv](https://docs.astral.sh/uv/).

Then run `./setup_mcp.sh`. This script assumes a
working `claude`, and will register the MCP with it:
this writes `.mcp.json` at the root of the project,
which `replay.py` passes to `claude`.

You can then put the MCP in your context
with `source .venv/bin/activate`.
