#!/bin/sh
# Build the TickLib proofs, replay the import, run the differential tests and audit the axioms.
set -eu
cd "$(dirname "$0")/.."
# Resolves the dependencies pinned in lake-manifest.json, then fetches Mathlib's
# prebuilt oleans (CI's lean-action only does this for the root package).
lake exe cache get
python3 .lake/packages/verity/scripts/setup_solc_import.py --output .lake/solidity-import/solc-0.8.34
lake build
python3 check/check_import.py
# A/B/C differential tests, as in the root check: run the imported model and the
# solc-compiled bytecode on the same inputs and compare results and reverts.
for f in wexp ticktoprice; do
  sh .lake/packages/verity/scripts/check_solidity_differential.sh \
    --config check/differential-$f.json --output out/differential-$f --cases 256 --seed 2438
done
mkdir -p out
lake env lean check/AxiomAudit.lean > out/axioms.txt
python3 - <<'PY'
import re
from pathlib import Path
text = Path("out/axioms.txt").read_text()
expected = {
    "TickLib.Proof.wExpIsMonotonic",
    "TickLib.Proof.wExpNotMonotonicBeyond",
    "TickLib.Proof.maxOutputIsWExpOfMaxInput",
    "TickLib.Proof.tickToPriceIsMonotonic",
    "TickLib.Proof.tickToPriceIsZeroAtZero",
    "TickLib.Proof.tickToPriceIsOneAtMaxTick",
    "TickLib.Proof.tickToPriceUsesPriceRoundingStep",
    "TickLib.Proof.tickToPriceAtMostWad",
    "TickLib.Proof.tickToPriceTotal",
    "tickLib.covered",
}
seen = set()
for name, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", text):
    extra = {a.strip() for a in axioms.split(",") if a.strip()} - {"propext", "Classical.choice", "Quot.sound"}
    assert not extra, (name, extra)
    seen.add(name)
assert seen == expected, ("missing/unexpected axiom audit", seen, expected)
print(text, end="")
PY
