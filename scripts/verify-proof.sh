#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
test -f Midnight/Proof.lean
mkdir -p out
# Build any newly generated supporting lemma modules.
lake build
# Elaborate the submitted theorem, even if the library root does not import it.
lake env lean -o .lake/build/lib/lean/Midnight/Proof.olean Midnight/Proof.lean
printf '%s\n' 'import Midnight.Proof' 'example : Midnight.Spec.updatePositionViewProperties := Midnight.updatePositionViewProperties' > out/ExactProofType.lean
lake env lean out/ExactProofType.lean
lake env lean check/AxiomAudit.lean > out/axioms.txt
python3 - <<'PYCODE'
import re
from pathlib import Path
text = Path("out/axioms.txt").read_text()
expected = {"Midnight.updatePositionViewProperties", "midnight.covered"}
seen = set()
for name, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", text):
    extra = {a.strip() for a in axioms.split(",") if a.strip()} - {"propext", "Classical.choice", "Quot.sound"}
    assert not extra, (name, extra)
    seen.add(name)
assert seen == expected, (seen, expected)
print(text, end="")
PYCODE
