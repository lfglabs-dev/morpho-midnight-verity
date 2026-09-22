#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
if [ ! -x .lake/solidity-import/solc-0.8.34 ]; then
  echo "missing .lake/solidity-import/solc-0.8.34" >&2
  echo "copy or link the pinned binary from the Verity checkout" >&2
  exit 1
fi
lake build
mkdir -p out
forge test --match-contract UpdatePositionViewDiffTest -vv
lake exe morpho_diff
lake env lean MorphoMidnight/AxiomAudit.lean > /tmp/morpho-axioms.txt
if grep -E 'sorryAx|native_decide|sorry' /tmp/morpho-axioms.txt; then
  echo "axiom audit failed" >&2
  exit 1
fi
echo "axiom audit:"
cat /tmp/morpho-axioms.txt
