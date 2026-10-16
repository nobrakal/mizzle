#!/bin/bash
set -euo pipefail
IFS=$'\n\t'

PROJ=$(pwd)
MCPGIT=rocq-mcp
MCPCOMMITID=d92fa9eaab78230a8b81f37b3a605672076ca22c

if [ -d "$MCPGIT" ]; then
    echo "Directory $MCPGIT exists, exiting"
    exit 1
fi

# Creating a virtual env
uv venv

# cloning the mcp git at a particular revision
git clone --revision=$MCPCOMMITID --depth=1 https://github.com/LLM4Rocq/rocq-mcp.git $MCPGIT
uv pip install -e $MCPGIT

# add the mcp to claude, with the local opam switch on its PATH so that it
# finds rocq and pet, and without needing the venv to be activated
claude mcp add --scope project rocq -- /bin/sh -c "PATH=\"$PROJ/_opam/bin:\$PATH\" exec $PROJ/.venv/bin/rocq-mcp"
