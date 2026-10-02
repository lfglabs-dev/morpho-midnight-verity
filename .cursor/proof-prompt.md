Read `AGENTS.md` and `check/README.md`, then generate a fresh Lean proof of
`Midnight.Spec.updatePositionViewProperties` in `Midnight/Proof.lean`, following
the repository instructions. Use compiler feedback until the proof passes
`sh scripts/verify-proof.sh`, and report the verification result.

Available shell tools: `sh scripts/doctor.sh` checks environment readiness,
`lake env lean Midnight/Proof.lean` gives compiler feedback, and
`sh scripts/verify-proof.sh` checks the exact theorem and its axioms.
If Lean MCP is enabled, use `lean_diagnostic_messages`, `lean_goal`,
`lean_hover_info`, and `lean_local_search` for diagnostics and theorem search.
Shell tools work without MCP.
