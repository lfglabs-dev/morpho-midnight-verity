# Morpho Lean environment

Run `sh scripts/setup.sh` to prepare pinned Lean 4.31.0, Verity, solc 0.8.34,
and Lean diagnostics MCP. `sh scripts/doctor.sh` verifies readiness.
Cursor install/start also require the Docker image marker. Use the built-in
Cursor Cloud MCP to inspect Build logs and trigger native test Builds.

Proof work must preserve Midnight/Import.lean, Midnight/Spec.lean, the toolchain,
and dependency pins. Run the existing `./check/check.sh` for full proof/import/
differential/axiom verification. Never use sorry, admit, custom axioms,
native_decide, or weaken a specification to make verification pass.

The separate `cursor/proof-sandbox` branch intentionally removes the existing
proof and supporting lemmas. On that branch, generate a new proof without
recovering removed proofs from history, GitHub, or another checkout.

The install hook preinstalls lean-lsp-mcp 0.31.0 with pinned dependencies.
`sh scripts/lean-mcp.sh` launches its stdio server. Use real diagnostics,
goal states, hover documentation, and local theorem search. MCP results do not
replace a kernel/axiom audit. `.cursor/mcp.json` configures Cursor IDE;
Cloud MCPs require enabling the stdio wrapper in account/team MCP settings with
the actual workspace path. Shell Lean works without optional MCP configuration.
