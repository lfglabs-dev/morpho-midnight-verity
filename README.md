# Morpho Midnight proof-generation sandbox

This branch keeps the deterministic Solidity import and the Certora specification
`Midnight.Spec.updatePositionViewProperties`, but removes the existing proof and
its supporting lemmas. The task is to generate a new kernel-checked proof.

Use the short [Cursor proof prompt](.cursor/proof-prompt.md) when submitting
this task. Select GPT-5.6 and the validated Build in the launch configuration;
the prompt delegates proof constraints to `AGENTS.md`.

The toolchain is Lean **4.31.0**, Verity
**9b472a8a48a9990337845f1720a20f374fa1e9cd**, and checksum-pinned solc **0.8.34**.
Lake dependencies and the Midnight Solidity submodule are pinned in git.

Cursor Cloud reads [.cursor/environment.json](.cursor/environment.json), with
[.cursor/Dockerfile](.cursor/Dockerfile) and `sh scripts/setup.sh` as install hook.
See [Cursor setup documentation](https://cursor.com/docs/cloud-agent/setup).
Cursor Builds currently use default-branch configuration; launching on a feature
branch may reuse the active Build. Verify the image marker before assuming the
branch Dockerfile was applied.

Local container workflow:

```sh
docker build -f .cursor/Dockerfile -t morpho-proof .
docker run --rm -v "$PWD:/workspace" -w /workspace morpho-proof sh scripts/setup.sh
# After generating Midnight/Proof.lean:
docker run --rm -v "$PWD:/workspace" -w /workspace morpho-proof sh scripts/verify-proof.sh
```

The verifier checks the theorem's axioms and rejects `sorryAx` and additional
axioms. `./check/check.sh` additionally checks import provenance and differential
execution after the proof is generated. See [check/README.md](check/README.md)
for the import's trust boundary.

## Agent diagnostics

`sh scripts/doctor.sh` checks the installed toolchain, pinned dependency, solc,
compiled import/specification, and MCP executable. Cursor install and startup
also require the Docker image marker so a default image cannot pass readiness.

`lean-lsp-mcp` 0.31.0 and its Python dependencies are pinned and preinstalled by
the install hook. `sh scripts/lean-mcp.sh` launches its stdio server; it provides
compiler diagnostics, goal states, hover information, and local theorem search.
`.cursor/mcp.json` configures Cursor IDE. Cursor Cloud custom MCP servers must be
enabled in the account/team MCP settings; the repo config alone does not enable
them. Configure the same stdio wrapper using the actual Cloud workspace path.
Shell-based compilation and verification work without enabling the MCP.

To exercise real diagnostics and proof goals:

```sh
.lake/lean-mcp/bin/python scripts/check-lean-mcp.py
```

The smoke test checks the unchanged Morpho specification, detects an intentionally
unfinished temporary example, and reads its goal. The temporary file is removed.
