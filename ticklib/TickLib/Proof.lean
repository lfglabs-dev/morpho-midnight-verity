import TickLib.Spec
import TickLib.Proof.Bridge

/-!
# The nine rules of `Spec.lean`, proved

Each theorem below proves the rule of the same name in `Spec.lean`, on the code
imported by `Import.lean`. The proofs are short because the work is done by the
three steps in `Proof/`:

```
tickLib.wExp x          (imported Solidity, 256-bit words)
   │  Proof/Execution.lean   run the imported body: it returns `wExpW x`
   ▼
wExpW x                 (a plain Lean function on words)
   │  Proof/Bridge.lean      on [-X*, X*] it equals `wExpVal x`
   │  (uses Proof/Signed.lean: word ops = integer ops while nothing overflows)
   ▼
wExpVal x               (the same formula on unbounded integers)
   │  Proof/Math.lean        `wExpVal_mono`: x ≤ y → wExpVal x ≤ wExpVal y
   ▼
wExpIsMonotonic         (this file)
```

`tickToPrice` follows the same chain: `tickW` in `Execution.lean`,
`tickToPrice_some` in `Bridge.lean`, then `priceOf_anti` and `wExpVal_mono`
in `Math.lean`.
-/

open Verity.Core TickLib.Proof.Bridge TickLib.Proof.Math TickLib.Proof.Execution TickLib.Proof.Signed
namespace TickLib.Proof

theorem wExpIsMonotonic : Spec.wExpIsMonotonic := by
  intro o w x y hxy h0 h1
  have hx1 : (x : Int) ≤ XSTAR := le_trans hxy h1
  have hy0 : -XSTAR ≤ (y : Int) := le_trans h0 hxy
  refine ⟨_, _, wExp_val o w x h0 hx1, wExp_val o w y hy0 h1, ?_⟩
  show (Uint256.ofNat _).val ≤ (Uint256.ofNat _).val
  rw [ofNat_val_of_lt (wExpVal_lt h0 hx1), ofNat_val_of_lt (wExpVal_lt hy0 h1)]
  exact wExpVal_mono hxy

theorem wExpNotMonotonicBeyond : Spec.wExpNotMonotonicBeyond := by
  intro o w
  rw [xstar_eq]
  have hX : (Int256.ofInt XSTAR : Int) = XSTAR := toInt_ofInt' (by unfold XSTAR; norm_num) (by unfold XSTAR; norm_num)
  have hX1 : (Int256.ofInt (XSTAR + 1) : Int) = XSTAR + 1 :=
    toInt_ofInt' (by unfold XSTAR; norm_num) (by unfold XSTAR; norm_num)
  refine ⟨_, Uint256.ofNat 0, wExp_val o w _ (by rw [hX]; unfold XSTAR; norm_num) (by rw [hX]), ?_, ?_⟩
  · rw [wExp_call, hX1]
    have h00 : (0 : Nat) = enc 0 := by decide
    unfold wExpW
    rw [h00, sltW_enc (inR_of (XSTAR + 1) (XSTAR + 1) le_rfl le_rfl (by unfold XSTAR; norm_num)
      (by unfold XSTAR; norm_num)) (inR_of 0 0 le_rfl le_rfl), decide_eq_false (by unfold XSTAR; norm_num),
      if_neg (by simp), wCore_enc (by unfold XSTAR; norm_num) (by unfold XSTAR; norm_num), expPos_overflow]
    rfl
  · show (Uint256.ofNat 0).val < (Uint256.ofNat (wExpVal (Int256.ofInt XSTAR))).val
    rw [hX, ofNat_val_of_lt (wExpVal_lt (by unfold XSTAR; norm_num) le_rfl)]
    unfold wExpVal; rw [if_neg (by unfold XSTAR; norm_num)]
    have := expPos_ge (x := XSTAR) (by unfold XSTAR; norm_num)
    show 0 % Uint256.modulus < _
    rw [Nat.zero_mod]; omega

theorem maxOutputIsWExpOfMaxInput : Spec.maxOutputIsWExpOfMaxInput := by
  intro o w
  have hm : (Int256.ofInt Spec.maxInput : Int) = 16817989975223754156 :=
    toInt_ofInt' (by unfold XSTAR Spec.maxInput; norm_num) (by unfold XSTAR Spec.maxInput; norm_num)
  rw [wExp_val o w _ (by rw [hm]; unfold XSTAR; norm_num) (by rw [hm]; unfold XSTAR; norm_num), hm,
    wExpVal_maxInput]
  rfl

theorem tickToPriceIsMonotonic : Spec.tickToPriceIsMonotonic := by
  intro o w t1 t2 p1 p2 hlt h1 h2
  obtain ⟨_, hp1⟩ := tickToPrice_some h1
  obtain ⟨ht2, hp2⟩ := tickToPrice_some h2
  have hlt' : t1.val < t2.val := hlt
  show p1.val ≤ p2.val
  rw [hp1, hp2]
  apply priceOf_anti
  apply wExpVal_mono
  unfold tickInput; nlinarith

theorem tickToPriceTotal : Spec.tickToPriceTotal := by
  intro o w tick ht
  exact ⟨_, by rw [tickToPrice_call, tickW_val ht]; rfl⟩

theorem tickToPriceIsZeroAtZero : Spec.tickToPriceIsZeroAtZero := by
  intro o w
  rw [tickToPrice_call, show (0 : Uint256).val = 0 from rfl, tickW_val (by norm_num)]
  have : priceOf (wExpVal (tickInput 0)) = 0 := by
    rw [show tickInput 0 = 16817989975223754156 by unfold tickInput; norm_num, wExpVal_maxInput]; decide
  rw [Option.map_some, this]; rfl

theorem tickToPriceIsOneAtMaxTick : Spec.tickToPriceIsOneAtMaxTick := by
  intro o w
  rw [tickToPrice_call, show (6744 : Uint256).val = 6744 from rfl, tickW_val (by norm_num)]
  have : priceOf (wExpVal (tickInput 6744)) = 1000000000000000000 := by
    rw [show tickInput 6744 = -16817989975223754156 by unfold tickInput; norm_num]
    unfold wExpVal; rw [if_pos (by norm_num), neg_neg]
    have h := wExpVal_maxInput
    unfold wExpVal at h; rw [if_neg (by norm_num)] at h
    rw [h]; decide
  rw [Option.map_some, this]; rfl

theorem tickToPriceUsesPriceRoundingStep : Spec.tickToPriceUsesPriceRoundingStep := by
  intro o w tick price h
  obtain ⟨_, hp⟩ := tickToPrice_some h
  rw [hp]
  unfold priceOf roundStep
  exact Nat.mul_mod_left _ _

theorem tickToPriceAtMostWad : Spec.tickToPriceAtMostWad := by
  intro o w tick price h
  obtain ⟨_, hp⟩ := tickToPrice_some h
  rw [hp]
  exact priceOf_le_wad _

end TickLib.Proof
