# Morpho Midnight × Verity

Proves the Certora rule
[`updatePositionViewProperties`](https://github.com/morpho-org/midnight/blob/96d31343e993329e7a593dde46516a2c0cbcd142/certora/specs/UpdatePositionView.spec)
on `Midnight.updatePositionView`, imported directly from the Solidity of
[midnight@96d31343](https://github.com/morpho-org/midnight/tree/96d31343e993329e7a593dde46516a2c0cbcd142).

- [Import.lean](Midnight/Import.lean): the Solidity import
- [Spec.lean](Midnight/Spec.lean): the rule `updatePositionViewProperties` as a definition, in the CVL vocabulary, without the CVL ghosts (not needed for a single call)
- [Proof.lean](Midnight/Proof.lean): the theorem that the rule holds (supporting lemmas in [Lemmas/](Midnight/Lemmas))
- [check/](check/README.md): what is trusted and how the import is checked

```sh
git submodule update --init --recursive
./check/check.sh
```

## Cursor Cloud environment

`.cursor/environment.json` uses `.cursor/Dockerfile` to install Lean 4.31.0.
The install hook prepares checksum-pinned solc 0.8.34, the committed Lake
dependencies, the imported model/specification, and lean-lsp-mcp 0.31.0.
Install and startup readiness checks reject Cursor's fallback/default image.

Cursor only activates Builds from the default branch; feature-branch draft
Builds can be tested but cannot be promoted. Keep this infrastructure on the
default branch and launch proof experiments on `cursor/proof-sandbox`.
That branch removes the old proof; this infrastructure change preserves it.
See `check/CURSOR_CLOUD_TEST.md` for native Build evidence and activation status.

`sh scripts/doctor.sh` checks local readiness. `sh scripts/lean-mcp.sh` runs
stdio Lean diagnostics. `.cursor/mcp.json` configures Cursor IDE; custom Cloud
MCPs additionally require account/team enablement. The server provides compiler
diagnostics and proof goals; shell verification remains available without MCP.
Run `.lake/lean-mcp/bin/python scripts/check-lean-mcp.py` for the diagnostic/goal
smoke test. Run the existing `./check/check.sh` for full verification.
