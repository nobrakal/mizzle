#!/bin/bash
set -euo pipefail
IFS=$'\n\t'

export OPAMYES=true

# Update the package list.
echo "Updating the list of available packages..."
opam update

# Create a local switch. (We assume opam 2 is installed.)
echo "Creating a local switch..."

# Repositories are registered globally by name, and opam refuses to register a
# name again with a different URL (e.g. a mirror). Reuse a repository that is
# already registered under that name; otherwise give its URL.
repo() {
  if opam repo list --all --short | grep -qx "$1"; then
    echo "$1"
  else
    echo "$1=$2"
  fi
}

opam switch create . --empty --repos "default,$(repo rocq-released https://rocq-prover.org/opam/released),$(repo iris-dev git+https://gitlab.mpi-sws.org/iris/opam.git)"
eval "$(opam env --set-switch)"

opam install ./mizzle.opam --deps-only

echo "Compiling..."
make
