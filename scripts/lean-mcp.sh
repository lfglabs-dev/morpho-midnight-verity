#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
export LEAN_PROJECT_PATH="$PWD"
export LEAN_LOG_LEVEL=NONE
exec .lake/lean-mcp/bin/lean-lsp-mcp "$@"
