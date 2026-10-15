import Lake
open Lake DSL

/-! TickLib monotonicity proofs. A separate package because the TickLib import
needs a newer Verity than the root `updatePositionView` proof is pinned to. -/
package ticklib where
  version := v!"0.1.0"

require verity from git "https://github.com/lfglabs-dev/verity" @ "10f697bbb52dd9273591490137fe20593db56dde"

/-- Midnight sources read by `solidity_import` (the shared submodule). -/
input_dir midnightSol where
  path := "../vendor/midnight/src"
  filter := .extension "sol"
  text := true

/-- Morpho's Certora harness importing the unmodified `TickLib.sol`. -/
input_dir midnightHarness where
  path := "../vendor/midnight/certora/helpers"
  filter := .extension "sol"
  text := true

@[default_target]
lean_lib «TickLib» where
  globs := #[.andSubmodules `TickLib]
  needs := #[midnightSol, midnightHarness]
