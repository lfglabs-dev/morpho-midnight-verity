#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
if [ "${1:-}" = --require-image ]; then
  test "$(cat /etc/morpho-proof-environment)" = morpho-lean-v4.31.0
fi
lean --version | grep -F 'version 4.31.0,'
lake --version
test "$(git -C .lake/packages/verity rev-parse HEAD)" = 9b472a8a48a9990337845f1720a20f374fa1e9cd
.lake/solidity-import/solc-0.8.34 --version | grep -F 'Version: 0.8.34+commit.80d5c536'
test -f .lake/build/lib/lean/Midnight/Import.olean
test -f .lake/build/lib/lean/Midnight/Spec.olean
.lake/lean-mcp/bin/lean-lsp-mcp --version
printf '%s\n' 'Morpho proof environment is ready.'
