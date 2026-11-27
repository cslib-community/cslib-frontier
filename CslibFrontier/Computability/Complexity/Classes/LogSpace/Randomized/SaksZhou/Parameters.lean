/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.Randomized.SaksZhou.Entry
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.NatSqrt
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.InputBit
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.NatPow

/-!
# Computing the parameters of the Saks–Zhou iteration

The iteration depth and precision are computed in logarithmic space from the length of a
read-only bit word. The grid denominator fits within the same budget. The binary limit for
enumerating all seeds uses space proportional to the seed length.

## Main definitions

* `saksZhouSpace` is the three-halves power of the logarithmic workspace with integer rounding.
* `saksZhouSeedCount` counts the seeds enumerated by the outer decision procedure.

## Main results

* `saksZhouSeedCount_inSpace` computes the exclusive seed limit in this workspace.
* `saksZhouDenominator_inSpace` computes the grid denominator in logarithmic space.
-/

public section

namespace Turing.MultiTapePTM.ConfigurationGraph

open MultiTapeTM MultiTapeTM.ComputableInSpace

/-- The integer workspace bound `(⌊log₂ n⌋+1)(⌊√(⌊log₂ n⌋+1)⌋+1)`. -/
@[expose] def saksZhouSpace (n : ℕ) : ℕ :=
  (Nat.log2 n + 1) * (Nat.sqrt (Nat.log2 n + 1) + 1)

/-- Number of packed integers enumerating all hash seeds and rounding shifts. -/
@[expose] def saksZhouSeedCount (clk n : ℕ) : ℕ :=
  let s := saksZhouLevels clk n
  let d := saksZhouPrecision clk n
  2 ^ (s * (3 * (2 * (5 * d)) - 1) + s * d)

/-- The input position counter fits in the workspace for the iteration. -/
theorem log2_le_saksZhouSpace (n : ℕ) : Nat.log2 n ≤ saksZhouSpace n := by
  simp only [saksZhouSpace]
  nlinarith [Nat.zero_le ((Nat.log2 n + 1) * Nat.sqrt (Nat.log2 n + 1))]

private theorem clockExponent_inSpace (clk : ℕ) :
    ComputableInSpace (fun w : List Bool => clk * (Nat.log2 w.length + 2) + 1) encBits encNat
      fun w => Nat.log2 w.length :=
  budget_natSucc (budget_natMul (budget_const clk) (budget_natAdd log2BitsLength (budget_const 2)))

/-- The recursion depth computed from the length of a read-only input. -/
theorem saksZhouLevels_inSpace (clk : ℕ) :
    ComputableInSpace (fun w : List Bool => saksZhouLevels clk w.length) encBits encNat
      fun w => Nat.log2 w.length :=
  budget_natSucc (budget_comp_linear natSqrt (clockExponent_inSpace clk))

/-- The number of fractional bits computed from the length of a read-only input. -/
theorem saksZhouPrecision_inSpace (clk : ℕ) :
    ComputableInSpace (fun w : List Bool => saksZhouPrecision clk w.length) encBits encNat
      fun w => Nat.log2 w.length :=
  budget_natAdd (budget_natMul (budget_const 5) (clockExponent_inSpace clk)) (budget_const 5)

/-- The retained number of bits grows at most linearly in the logarithmic input length. -/
theorem saksZhouPrecision_le (clk n : ℕ) :
    saksZhouPrecision clk n ≤ (10 * clk + 10) * (Nat.log2 n + 1) := by
  simp only [saksZhouPrecision]
  nlinarith

/-- The binary grid denominator uses space logarithmic in the input length. -/
theorem saksZhouDenominator_inSpace (clk : ℕ) :
    ComputableInSpace (fun w : List Bool => 2 ^ saksZhouPrecision clk w.length) encBits encNat
      fun w => Nat.log2 w.length :=
  budget_twoPow (saksZhouPrecision_inSpace clk) ⟨10 * clk + 10, fun w =>
    saksZhouPrecision_le clk w.length⟩

/-- The exclusive seed limit fits within space proportional to the packed seed width. -/
theorem saksZhouSeedCount_inSpace (clk : ℕ) :
    ComputableInSpace (fun w : List Bool => saksZhouSeedCount clk w.length) encBits encNat
      fun w => saksZhouSpace w.length := by
  have hs := (saksZhouLevels_inSpace clk).mono_le fun w => log2_le_saksZhouSpace w.length
  have hd := (saksZhouPrecision_inSpace clk).mono_le fun w => log2_le_saksZhouSpace w.length
  refine budget_twoPow (budget_natAdd (budget_natMul hs (budget_natSub
    (budget_natMul (budget_const 3)
      (budget_natMul (budget_const 2) (budget_natMul (budget_const 5) hd)))
      (budget_const 1))) (budget_natMul hs hd)) ⟨155 * (2 * clk + 2) ^ 2, fun w => ?_⟩
  have h := Cslib.Complexity.saksZhou_seed_budget_le clk (Nat.log2 w.length)
  unfold saksZhouSpace
  dsimp only [saksZhouPrecision, saksZhouLevels] at *
  nlinarith

end Turing.MultiTapePTM.ConfigurationGraph
