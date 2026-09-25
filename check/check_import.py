#!/usr/bin/env python3
"""Re-elaborate from current Solidity and reject stale Lake imports/provenance."""
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
source = (ROOT / "Midnight/Import.lean").read_text()
marker = "solidity_import midnight"
assert source.count(marker) == 1, "expected one declarative Midnight import"
replay = ROOT / ".lake/import-replay/Check.lean"
replay.parent.mkdir(parents=True, exist_ok=True)
(ROOT / "out").mkdir(exist_ok=True)
replay.write_text(
    "import Midnight.Import\nimport Compiler.SolidityImport.Differential\n"
    + source.replace(marker, "namespace Replay\nsolidity_import fresh")
    + "\nend Replay\n"
    + "example : Replay.fresh.model = midnight.model := by rfl\n"
    + "example : Replay.fresh.sourceDigest = midnight.sourceDigest := by decide\n"
    + '#eval IO.FS.writeFile "out/report.txt" Replay.fresh.report.toText\n'
    + '#eval IO.FS.writeFile "out/model.txt" (toString (repr Replay.fresh.model) ++ "\\n")\n'
    + '#eval IO.FS.writeFile "out/functions.txt" '
    + "(Compiler.CompilationModel.SolidityImport.Differential.statusText Replay.fresh.model Replay.fresh.report)\n"
)
# The default target does not build the status driver; `lake env lean` would use a stale olean.
subprocess.run(["lake", "build", "Compiler.SolidityImport.Differential"], cwd=ROOT, check=True)
subprocess.run(["lake", "env", "lean", str(replay)], cwd=ROOT, check=True)


def portable_report(path: Path) -> list[str]:
    # The two official Linux/macOS binaries have different verified checksums.
    return [line for line in path.read_text().splitlines() if not line.startswith("solcSha256 ")]


# The proofs depend on the exact model shape; importer refactors must reproduce it.
if (ROOT / "out/model.txt").read_text() != (ROOT / "check/provenance/model.txt").read_text():
    raise SystemExit("imported model changed: review out/model.txt against check/provenance/model.txt")
if portable_report(ROOT / "out/report.txt") != portable_report(ROOT / "check/provenance/report.txt"):
    raise SystemExit("provenance changed: review out/report.txt against check/provenance/report.txt")
if (ROOT / "out/functions.txt").read_text() != (ROOT / "check/provenance/functions.txt").read_text():
    raise SystemExit("function status changed: review out/functions.txt against check/provenance/functions.txt")
print("fresh import equals the proved model; provenance matches")
