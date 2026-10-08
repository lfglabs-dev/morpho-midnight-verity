#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
lean --version
lake --version
test "$(cat lean-toolchain)" = leanprover/lean4:v4.31.0
git submodule update --init --recursive
# Use the committed manifest; do not move dependency revisions.
lake env lean --version
test "$(git -C .lake/packages/verity rev-parse HEAD)" = 9b472a8a48a9990337845f1720a20f374fa1e9cd
python3 .lake/packages/verity/scripts/setup_solc_import.py --output .lake/solidity-import/solc-0.8.34
lake exe cache get Mathlib.Tactic
lake build Midnight.Import Midnight.Spec Compiler.SolidityImport.Proofs
# Install the diagnostic server into checkout-local state captured by the Build.
python3 -m venv .lake/lean-mcp
.lake/lean-mcp/bin/python -m pip install --disable-pip-version-check -r scripts/lean-mcp-requirements.txt
.lake/lean-mcp/bin/lean-lsp-mcp --version
sh scripts/doctor.sh
