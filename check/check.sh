#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
if [ ! -d .lake/packages/verity ]; then
  lake update
fi
python3 .lake/packages/verity/scripts/setup_solc_import.py --output .lake/solidity-import/solc-0.8.34
lake build
python3 check/check_import.py
sh .lake/packages/verity/scripts/check_solidity_differential.sh \
  --config check/differential.json --output out/differential --cases 256 --seed 2438
lake env lean check/AxiomAudit.lean > out/axioms.txt
python3 - <<'PY'
import re
from pathlib import Path
text = Path("out/axioms.txt").read_text()
expected = {
    "Midnight.updatePositionViewProperties",
    "midnight.covered",
}
seen = set()
for name, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", text):
    extra = {a.strip() for a in axioms.split(",") if a.strip()} - {"propext", "Classical.choice", "Quot.sound"}
    assert not extra, (name, extra)
    seen.add(name)
assert seen == expected, ("missing/unexpected axiom audit", seen, expected)
print(text, end="")
PY
