# Morpho Midnight proof-generation sandbox

This branch keeps the deterministic Solidity import and the Certora specification
`Midnight.Spec.updatePositionViewProperties`, but removes the existing proof and
its supporting lemmas. The task is to generate a new kernel-checked proof.

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
