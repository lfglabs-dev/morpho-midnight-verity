#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
lean --version
lake --version
test "$(cat lean-toolchain)" = leanprover/lean4:v4.31.0
git submodule update --init --recursive
# Use the committed manifest; do not move dependency revisions.
lake env lean --version
python3 .lake/packages/verity/scripts/setup_solc_import.py --output .lake/solidity-import/solc-0.8.34
lake exe cache get
lake build Midnight.Import Midnight.Spec
