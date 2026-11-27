/-
Copyright (c) 2026 Phillipp Schoppmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Phillipp Schoppmann
-/

module

public import CslibFrontier.Crypto.Protocols.MPC.InputConsistency

/-!
# Concrete Tests for Two-Party Input Consistency: Shift Attack and MAC Repair

Non-vacuous concrete evaluations and theorem instantiations exercising
`Cslib.Crypto.Protocols.MPC.InputConsistency`:

1. **Corrupt additive-shift attack on `f(x) = x * (x - 1)` (`q = 5` and `q = 7`):**
   - Concrete two-party additive shares of `x = 0` and `x = 1` over `ZMod 5` and `ZMod 7`,
     verifying `f(0 + 1) = 0` and `f(1 + 1) = 2 ≠ 0`.
   - Concrete instantiations of the left-right distinguishing games (`advantage = 1` in the real
     world vs `0` in the ideal world) and hidden-bit recovery games (`Pr = 1` vs `Pr = 1 / 2`).
2. **Characteristic-`2` edge case (`q = 2`):**
   - Demonstrates why `q > 2` is necessary for the `δ = 1` shift attack: in `ZMod 2`, `2 = 0`, so
     `f(0 + 1) = 0` and `f(1 + 1) = 0`, leaving the shifted output invariant on `{0, 1}`.
3. **Random-MAC and random-linear-combination input-authentication repair (`q = 5` and `q = 7`):**
   - Non-vacuous two-party `SPDZ.AuthShare 5 2` witness built by `mkAuthShare2`,
     verifying honest check acceptance, detection of an unauthenticated shift `(δ_x = 1, δ_t = 2)`
     by `SPDZ.AuthShare.tamperParty`, and exact `1 / q` forgery probability (`Pr = 1 / 5` for
     `q = 5`, `Pr = 1 / 7` for `q = 7`).
   - Non-vacuous `k = 3` vector witness `LinearCombAuthVec2 (ZMod 5) 3`, verifying honest
     completeness (`Pr = 1`), exact `1 / q` soundness (`Pr = 1 / 5` for `q = 5`, `Pr = 1 / 7`
     for `q = 7`), and `≤ 2 / 5` batched scalar-MAC soundness.
-/

public section

namespace CslibFrontierTests.Crypto.MPCInputConsistency

open Cslib Cslib.Probability Cslib.ProbComp Cslib.Crypto
open Cslib.Crypto.Protocols.MPC Cslib.Crypto.Protocols.MPC.InputConsistency
open scoped ENNReal NNReal

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-! ### 1. Concrete `δ = 1` shift attack over `ZMod 5` and `ZMod 7` -/

/-- Valid additive sharing `(3, 2)` of `0` in `ZMod 5`. -/
def shareZeroMod5 : AdditiveShare2 (ZMod 5) := ⟨3, 2⟩

/-- Valid additive sharing `(4, 2)` of `1` in `ZMod 5`. -/
def shareOneMod5 : AdditiveShare2 (ZMod 5) := ⟨4, 2⟩

example : shareZeroMod5.IsValidFor 0 := by
  dsimp [AdditiveShare2.IsValidFor, AdditiveShare2.reconstruct, shareZeroMod5]
  decide

example : shareOneMod5.IsValidFor 1 := by
  dsimp [AdditiveShare2.IsValidFor, AdditiveShare2.reconstruct, shareOneMod5]
  decide

example : evalShiftedBitCheck shareZeroMod5 0 = 0 ∧ evalShiftedBitCheck shareOneMod5 0 = 0 := by
  decide

example : evalShiftedBitCheck shareZeroMod5 1 = 0 := by decide

example : evalShiftedBitCheck shareOneMod5 1 = 2 := by decide

example : (2 : ZMod 5) ≠ 0 := by decide

example : (2 : ZMod 7) ≠ 0 := by decide

example :
    let D : ZMod 5 → ProbComp Bool := fun z => return shiftOneDistinguisher z
    Game.advantage
      (ProbComp.eval (naiveBitCheckRealLRGame 5 1 D false))
      (ProbComp.eval (naiveBitCheckRealLRGame 5 1 D true)) = 1 :=
  advantage_naiveBitCheckRealLRGame_shiftOne (q := 5) (by decide)

example :
    let D : ZMod 7 → ProbComp Bool := fun z => return shiftOneDistinguisher z
    Game.advantage
      (ProbComp.eval (naiveBitCheckIdealLRGame 7 D false))
      (ProbComp.eval (naiveBitCheckIdealLRGame 7 D true)) = 0 :=
  advantage_naiveBitCheckIdealLRGame 7 _

example : Pr[naiveBitCheckRealGuessGame 5] = 1 :=
  probability_naiveBitCheckRealGuessGame (q := 5) (by decide)

example : Pr[naiveBitCheckRealGuessGame 7] = 1 :=
  probability_naiveBitCheckRealGuessGame (q := 7) (by decide)

example :
    Pr[naiveBitCheckIdealGuessGame 5 (fun _ => return true)] = 1 / 2 :=
  probability_naiveBitCheckIdealGuessGame 5 (fun _ => return true)

example :
    Game.advantage
      (ProbComp.eval (naiveBitCheckRealGuessGame 7))
      (ProbComp.eval (naiveBitCheckIdealGuessGame 7 (fun _ => return false))) = 1 / 2 :=
  advantage_naiveBitCheckGuessGame (q := 7) (by decide) (fun _ => return false)

/-! ### 2. Characteristic-`2` edge case (`q = 2`): why `q > 2` is needed -/

/-- Valid additive sharing `(1, 1)` of `0` in `ZMod 2`. -/
def shareZeroMod2 : AdditiveShare2 (ZMod 2) := ⟨1, 1⟩

/-- Valid additive sharing `(1, 0)` of `1` in `ZMod 2`. -/
def shareOneMod2 : AdditiveShare2 (ZMod 2) := ⟨1, 0⟩

example : shareZeroMod2.IsValidFor 0 ∧ shareOneMod2.IsValidFor 1 := by
  dsimp [AdditiveShare2.IsValidFor, AdditiveShare2.reconstruct, shareZeroMod2, shareOneMod2]
  decide

/-- In `ZMod 2`, `2 = 0`, so `f(1 + 1) = 0`: the `δ = 1` shift reveals no information about `x`. -/
example :
    evalShiftedBitCheck shareZeroMod2 1 = 0 ∧
    evalShiftedBitCheck shareOneMod2 1 = 0 := by
  decide

/-! ### 3. Random-MAC and random-linear-combination repair (`q = 5` and `q = 7`) -/

/-- Authentic two-party SPDZ sharing of `x = 1` under MAC key `α = 3` in `ZMod 5`:
value shares `(2, 1 - 2) = (2, 4)` and MAC shares `(1, 3 - 1) = (1, 2)`, so `x = 1` and
`t = 3 = 3 * 1`. -/
def authShareMod5 : SPDZ.AuthShare 5 2 := mkAuthShare2 3 1 2 1

example : authShareMod5.valShares = ![2, 4] ∧ authShareMod5.macShares = ![1, 2] := by decide

example : authShareMod5.Valid 3 := valid_mkAuthShare2 3 1 2 1

/-- Tampering with `(δ_x = 1, δ_t = 2)` fails the MAC check under `α = 3` (`3 * 1 ≠ 2` in
`ZMod 5`). -/
example : ¬ (authShareMod5.tamperParty 1 1 2).Valid 3 := by decide

/-- Tampering with `(δ_x = 1, δ_t = 3)` passes only because `α * δ_x = δ_t`. -/
example : (authShareMod5.tamperParty 1 1 3).Valid 3 := by decide

/-- The same conclusions through `SPDZ.AuthShare.valid_tamperParty_iff`. -/
example : ¬ (authShareMod5.tamperParty 1 1 2).Valid 3 ∧ (authShareMod5.tamperParty 1 1 3).Valid 3 :=
  ⟨fun h => absurd ((SPDZ.AuthShare.valid_tamperParty_iff (valid_mkAuthShare2 3 1 2 1) 1 1 2).mp h)
      (by decide),
    (SPDZ.AuthShare.valid_tamperParty_iff (valid_mkAuthShare2 3 1 2 1) 1 1 3).mpr (by decide)⟩

example : Pr[macSingleCheckGame 5 1 0 0] = 1 :=
  probability_macSingleCheckGame_honest 5 1

example : Pr[macSingleCheckGame 5 1 1 2] = 1 / 5 :=
  probability_macSingleCheckGame_eq (q := 5) 1 (by decide)

example : Pr[macSingleCheckGame 7 1 1 2] = 1 / 7 :=
  probability_macSingleCheckGame_eq (q := 7) 1 (by decide)

/-- Authentic `k = 3` vector sharing over `ZMod 5` under linear-combination key `r = ![2, 1, 4]`:
`x = ![1, 3, 2]`, `t = 2*1 + 1*3 + 4*2 = 13 ≡ 3 (mod 5)`. -/
def authVecMod5 : LinearCombAuthVec2 (ZMod 5) 3 :=
  ⟨![⟨2, 4⟩, ⟨1, 2⟩, ⟨4, 3⟩], ⟨1, 2⟩⟩

example : authVecMod5.IsValidFor ![2, 1, 4] := by
  dsimp [LinearCombAuthVec2.IsValidFor, LinearCombAuthVec2.macTag,
    LinearCombAuthVec2.secretVec, AdditiveShare2.reconstruct, authVecMod5]
  decide

/-- Nonzero input shift `δ = ![0, 1, 0]` with `δ_t = 0` fails under `r = ![2, 1, 4]`. -/
example : ¬ (authVecMod5.tamper1 ![0, 1, 0] 0).IsValidFor ![2, 1, 4] := by
  dsimp [LinearCombAuthVec2.IsValidFor, LinearCombAuthVec2.tamper1,
    LinearCombAuthVec2.macTag, LinearCombAuthVec2.secretVec,
    AdditiveShare2.shiftShare1, AdditiveShare2.reconstruct, authVecMod5]
  decide

example : Pr[vecLinearCombCheckGame 5 3 ![1, 3, 2] 0 0] = 1 :=
  probability_vecLinearCombCheckGame_honest 5 3 ![1, 3, 2]

example : Pr[vecLinearCombCheckGame 5 3 ![1, 3, 2] ![0, 1, 0] 0] = 1 / 5 :=
  probability_vecLinearCombCheckGame_eq (q := 5) ![1, 3, 2] (by decide) 0

example : Pr[vecLinearCombCheckGame 7 3 ![1, 3, 2] ![0, 1, 0] 0] = 1 / 7 :=
  probability_vecLinearCombCheckGame_eq (q := 7) ![1, 3, 2] (by decide) 0

example : Pr[vecBatchMacCheckGame 5 3 ![1, 3, 2] 0 0] = 1 :=
  probability_vecBatchMacCheckGame_honest 5 3 ![1, 3, 2]

example : Pr[vecBatchMacCheckGame 5 3 ![1, 3, 2] ![0, 1, 0] ![0, 0, 0]] ≤ 2 / 5 :=
  probability_vecBatchMacCheckGame_le (q := 5) ![1, 3, 2] (by decide) ![0, 0, 0]

end CslibFrontierTests.Crypto.MPCInputConsistency
