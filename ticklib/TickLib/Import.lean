import Compiler.SolidityImport.Import

/-!
`TickLib.wExp` and `TickLib.tickToPrice` at `morpho-org/midnight@96d31343`,
imported through Morpho's own Certora harness `certora/helpers/TickLibWrapper.sol`,
which calls the unmodified `src/libraries/TickLib.sol`.
-/

solidity_import tickLib from "../vendor/midnight" entry "certora/helpers/TickLibWrapper.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract TickLibWrapper
  function wExp(int256)
  function tickToPrice(uint256)
