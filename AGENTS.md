# Proof generation

This branch intentionally removes the existing Morpho proof and its supporting
lemmas. Keep Midnight/Import.lean, Midnight/Spec.lean, lean-toolchain, and the
committed lake manifest unchanged. Do not retrieve old proofs from git history,
GitHub, or another checkout. Verity/mathlib dependency lemmas are allowed.

Run `sh scripts/setup.sh` to prepare the pinned importer and Lean dependencies.
Generate `Midnight/Proof.lean` with theorem
`Midnight.updatePositionViewProperties : Midnight.Spec.updatePositionViewProperties`.
Compile frequently with `lake env lean Midnight/Proof.lean` and use the diagnostics
to correct your work. Supporting new lemmas may go in Midnight/Lemmas/.
Never use sorry, admit, custom axioms, native_decide, or weaken the specification.
Run `sh scripts/verify-proof.sh`; a build alone does not certify absence of sorry.
Add `import Midnight.Proof` to Midnight.lean once the proof passes.

Cursor Cloud: `.cursor/environment.json` references `.cursor/Dockerfile`.
The image installs Lean 4.31.0; the install hook prepares the checkout.
Confirm `/etc/morpho-proof-environment` exists before claiming that Cursor used
this image. Report separately an image build, environment provisioning, and
successful theorem verification. If Cursor uses a default-branch snapshot,
report it and test the Dockerfile explicitly rather than claiming automatic use.
