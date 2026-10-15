import TickLib.Import

/-!
# The Certora rules for `TickLib`, on the imported Solidity

[certora/specs/TickToPrice.spec](https://github.com/morpho-org/midnight/blob/96d31343e993329e7a593dde46516a2c0cbcd142/certora/specs/TickToPrice.spec)
and [TickToPriceIsMonotonic.spec](https://github.com/morpho-org/midnight/blob/96d31343e993329e7a593dde46516a2c0cbcd142/certora/specs/TickToPriceIsMonotonic.spec),
stated on `tickLib.wExp` and `tickLib.tickToPrice`. The import generates both from
Morpho's harness `certora/helpers/TickLibWrapper.sol`, which calls the unmodified
`src/libraries/TickLib.sol`. A call returns `none` when it reverts.

`Proof.lean` proves every statement below.

## Differences with the CVL

- **No ghost axiom.** `TickToPriceIsMonotonic.spec` summarizes `wExp` by a ghost
  with `axiom forall x y. x <= y => summaryWExp(x) <= summaryWExp(y)` over all
  `int256`. That axiom is false for the real `wExp`: see `wExpNotMonotonicBeyond`.
  Here `tickToPriceIsMonotonic` is about the imported code, `wExp` included.
- **One monotonicity rule for `wExp`**, over its exact maximal range
  `[-X*, X*]`, instead of the five step rules `wExpIsMonotonicOn*`,
  `expRIsMonotonicWithinSegment` and `qIncreasesByZeroOrOne` on `[-maxInput, maxInput]`.
- **`tickToPriceTotal`** is new: `tickToPrice` succeeds on every valid tick, so
  the `some` hypotheses of the other rules are not vacuous.
-/

open Compiler.CompilationModel.Denote
open Verity.Core
namespace TickLib.Spec

/-- `X* = 135999161806159974428`, the largest input where `wExp` does not overflow:
`expR << q` still fits in 256 bits. -/
def XSTAR : Int := 135999161806159974428

/-- `maxInput() = LN_ONE_PLUS_DELTA * (MAX_TICK / 2)`. -/
def maxInput : Int := 4987541511039073 * (6744 / 2)

/-- `maxOutput() = 20134595243400876315901952`. -/
def maxOutput : Nat := 20134595243400876315901952

/-- `wExp` is non-decreasing on `[-X*, X*]`, and succeeds there. This is the
largest such interval: `wExp(X* + 1) = 0` (`wExpNotMonotonicBeyond`), and
`wExp(-X* - 1) = 1e36 / wExp(X* + 1)` divides by zero. -/
def wExpIsMonotonic : Prop :=
  ∀ (oracle : DenoteOracle) (world : Verity.ContractState) (x y : Int256),
    (x : Int) ≤ y → -XSTAR ≤ (x : Int) → (y : Int) ≤ XSTAR →
    ∃ wx wy, tickLib.wExp oracle world x = some wx ∧ tickLib.wExp oracle world y = some wy ∧ wx ≤ wy

/-- `wExp(X*) > wExp(X* + 1)`, both calls succeeding: `wExp` is not monotone on all
of `int256`, so the ghost axiom of `TickToPriceIsMonotonic.spec` does not hold. -/
def wExpNotMonotonicBeyond : Prop :=
  ∀ (oracle : DenoteOracle) (world : Verity.ContractState),
    ∃ a b, tickLib.wExp oracle world (Int256.ofInt XSTAR) = some a ∧
      tickLib.wExp oracle world (Int256.ofInt (XSTAR + 1)) = some b ∧ b < a

/-- `rule maxOutputIsWExpOfMaxInput() { assert maxOutput() == wExp(maxInput()); }` -/
def maxOutputIsWExpOfMaxInput : Prop :=
  ∀ (oracle : DenoteOracle) (world : Verity.ContractState),
    tickLib.wExp oracle world (Int256.ofInt maxInput) = some (Uint256.ofNat maxOutput)

/-- `rule tickToPriceIsMonotonic(uint256 tick1, uint256 tick2)
{ assert tick1 < tick2 => tickToPrice(tick1) <= tickToPrice(tick2); }`, for all
ticks, without the ghost axiom on `wExp`. -/
def tickToPriceIsMonotonic : Prop :=
  ∀ (oracle : DenoteOracle) (world : Verity.ContractState) (tick1 tick2 : Uint256) (p1 p2 : Uint256),
    tick1 < tick2 →
    tickLib.tickToPrice oracle world tick1 = some p1 →
    tickLib.tickToPrice oracle world tick2 = some p2 →
    p1 ≤ p2

/-- `rule tickToPriceIsZeroAtZero() { assert tickToPrice(0) == 0; }` -/
def tickToPriceIsZeroAtZero : Prop :=
  ∀ (oracle : DenoteOracle) (world : Verity.ContractState),
    tickLib.tickToPrice oracle world 0 = some 0

/-- `rule tickToPriceIsOneAtMaxTick() { assert tickToPrice(maxTick()) == 10 ^ 18; }` -/
def tickToPriceIsOneAtMaxTick : Prop :=
  ∀ (oracle : DenoteOracle) (world : Verity.ContractState),
    tickLib.tickToPrice oracle world 6744 = some 1000000000000000000

/-- `rule tickToPriceUsesPriceRoundingStep(uint256 tick)
{ assert tickToPrice(tick) % priceRoundingStep() == 0; }` -/
def tickToPriceUsesPriceRoundingStep : Prop :=
  ∀ (oracle : DenoteOracle) (world : Verity.ContractState) (tick price : Uint256),
    tickLib.tickToPrice oracle world tick = some price → price.val % 100000000000 = 0

/-- `rule tickToPriceAtMostWad(uint256 tick) { assert tickToPrice(tick) <= 10 ^ 18; }` -/
def tickToPriceAtMostWad : Prop :=
  ∀ (oracle : DenoteOracle) (world : Verity.ContractState) (tick price : Uint256),
    tickLib.tickToPrice oracle world tick = some price → price.val ≤ 1000000000000000000

/-- `tickToPrice` succeeds on every tick up to `MAX_TICK = 6744`. -/
def tickToPriceTotal : Prop :=
  ∀ (oracle : DenoteOracle) (world : Verity.ContractState) (tick : Uint256),
    tick.val ≤ 6744 → ∃ price, tickLib.tickToPrice oracle world tick = some price

end TickLib.Spec
