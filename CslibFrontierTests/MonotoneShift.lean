/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Computability.Circuit.Monotone.Shift

/-!
# Client tests for monotone cyclic shift and permutation circuit bounds

Exercises the public API of `CslibFrontier.Computability.Circuit.Monotone.Shift` under ordinary
`module` imports: concrete evaluations of `oneHotShiftCircuit` and `dualRailShiftCircuit` at
`n = 4, q = 2`, a concrete positive `ComputesMonotonePerm` circuit witness at `n = 2, q = 1`,
boundary checks (`q = 0`, non-antichain comparable codewords, and duplicate singleton-antichain
codewords at `n = 2, q = 1`), and concrete instantiations of Theorem 1 and Theorem 3 + Permutation
Corollary at `n = 8, q = 2`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.MonotoneShift

open Cslib.Circuits Cslib.Circuits.Monotone Finset

/-- Four 2-bit blocks: `x₀ = (1, 0)`, `x₁ = (0, 1)`, `x₂ = (1, 1)`, `x₃ = (0, 0)`. -/
private def sampleVec : Fin (4 * 2) → Bool :=
  ![true, false, false, true, true, true, false, false]

-- Concrete right cyclic shift by `k = 1` moves `x₃ = (0,0)` to block 0, `x₀ = (1,0)` to block 1,
-- `x₁ = (0,1)` to block 2, and `x₂ = (1,1)` to block 3.
example :
    (oneHotShiftCircuit 4 2).eval interpretation
        (Fin.append sampleVec (oneHotShiftAntichain 4 1)) =
      ![false, false, true, false, false, true, true, true] := by
  rw [computesMonotoneShift_oneHotShiftCircuit]
  decide

-- Concrete right cyclic shift by `k = 3` on the minimal-width (`2 * ⌈log₂ 4⌉ = 4`) dual-rail
-- antichain `dualRailShiftAntichain 4`, together with its exact gate count `3 * 2 * 4 * 2 = 48`.
example :
    (dualRailShiftCircuit 4 2 (Nat.clog 2 4) le_rfl).eval interpretation
        (Fin.append sampleVec (dualRailShiftAntichain 4 3)) =
      ![false, true, true, true, false, false, true, false] ∧
    (dualRailShiftCircuit 4 2 (Nat.clog 2 4) le_rfl).program.cost binaryCost = 48 := by
  refine ⟨?_, ?_⟩
  · rw [computesMonotoneShift_dualRailShiftCircuit]
    decide
  · rw [cost_dualRailShiftCircuit]
    decide

-- Sergeev's p. 2 width convention `b = ⌊log₂ 4⌋ + 1 = 3` (`m = 6`) also forms an injective
-- antichain and uses the exact same `48` monotone binary gates.
example :
    Function.Injective (dualRailShiftCode 4 3) ∧
    IsAntichain (· ≤ ·) (Set.range (dualRailShiftCode 4 3)) ∧
    (dualRailShiftCircuit 4 2 3 (by decide)).eval interpretation
        (Fin.append sampleVec (dualRailShiftCode 4 3 2)) =
      ![true, true, false, false, true, false, false, true] ∧
    (dualRailShiftCircuit 4 2 3 (by decide)).program.cost binaryCost = 48 := by
  refine ⟨injective_dualRailShiftCode (by decide),
    isAntichain_range_dualRailShiftCode (by decide), ?_, ?_⟩
  · rw [computesMonotoneShift_dualRailShiftCircuit]
    decide
  · rw [cost_dualRailShiftCircuit]
    decide

-- Boundary `q = 0`: zero-width blocks require `0` binary gates.
example : (oneHotShiftCircuit 4 0).program.cost binaryCost = 0 := by
  have h := cost_oneHotShiftCircuit_le 4 0
  omega

/-- Encoding the `2! = 2` permutations of `Fin 2` via `π ↦ dualRailShiftCode 2 1 (π.symm 0)`. -/
private def permTwoCode (π : Equiv.Perm (Fin 2)) : Fin 2 → Bool :=
  dualRailShiftCode 2 1 (π.symm 0)

-- Concrete positive witness for `ComputesMonotonePerm` at `n = 2, q = 1`: every permutation of
-- `Fin 2` is a cyclic shift (`cyclicShiftPerm (π.symm 0) = π`), exercising `ComputesMonotonePerm`,
-- `ComputesMonotonePerm.injective_and_isAntichain`, and
-- `mul_sum_clog_le_cost_of_computesMonotonePerm`.
example :
    ComputesMonotonePerm (dualRailShiftCircuit 2 1 1 (by decide)) permTwoCode ∧
    Function.Injective permTwoCode ∧
    IsAntichain (· ≤ ·) (Set.range permTwoCode) ∧
    1 ≤ (dualRailShiftCircuit 2 1 1 (by decide)).program.cost binaryCost ∧
    (dualRailShiftCircuit 2 1 1 (by decide)).program.cost binaryCost = 6 := by
  have fin2 : ∀ u : Fin 2, u = 0 ∨ u = 1 := fun ⟨v, hv⟩ => by
    rcases v with _ | _ | _
    · exact Or.inl rfl
    · exact Or.inr rfl
    · omega
  have hπ_all : ∀ π : Equiv.Perm (Fin 2), cyclicShiftPerm (π.symm 0) = π := by
    intro π
    have h0 : π (π.symm 0) = 0 := π.apply_symm_apply 0
    have hne : π 0 ≠ π 1 := π.injective.ne (by decide)
    ext j
    rcases fin2 (π.symm 0) with hk | hk <;> rw [hk] at h0 ⊢ <;> rcases fin2 j with rfl | rfl
    · rw [h0]; decide
    · rcases fin2 (π 1) with hp | hp
      · exact absurd (h0.trans hp.symm) hne
      · rw [hp]; decide
    · rcases fin2 (π 0) with hp | hp
      · exact absurd (hp.trans h0.symm) hne
      · rw [hp]; decide
    · rw [h0]; decide
  have hperm : ComputesMonotonePerm (dualRailShiftCircuit 2 1 1 (by decide)) permTwoCode := by
    intro X π
    have hshift := computesMonotoneShift_dualRailShiftCircuit 2 1 1 (by decide) X (π.symm 0)
    change (dualRailShiftCircuit 2 1 1 (by decide)).eval interpretation
        (Fin.append X (permTwoCode π)) = cyclicShiftVec X (π.symm 0) at hshift
    rw [hshift, cyclicShiftVec, hπ_all π]
  have hanti := hperm.injective_and_isAntichain (by decide)
  have hlb : 1 ≤ (dualRailShiftCircuit 2 1 1 (by decide)).program.cost binaryCost :=
    calc 1 = 1 * (∑ t ∈ Icc 1 2, Nat.clog 2 t) := by decide
      _ ≤ (dualRailShiftCircuit 2 1 1 (by decide)).program.cost binaryCost :=
        mul_sum_clog_le_cost_of_computesMonotonePerm hperm
  refine ⟨hperm, hanti.1, hanti.2, hlb, ?_⟩
  rw [cost_dualRailShiftCircuit]
  decide

/-- Comparable distinct codewords `![false, true] < ![true, true]` at `n = 2, q = 1`. -/
private def comparableCode : Fin 2 → Fin 2 → Bool
  | 0 => ![false, true]
  | 1 => ![true, true]

-- Boundary check: comparable codewords cannot be implemented by any monotone shift circuit.
example : ¬ ∃ c : Circuit signature (2 * 1 + 2) (2 * 1),
    ComputesMonotoneShift c comparableCode := by
  rintro ⟨c, hc⟩
  exact hc.not_le (by decide) (by decide : (0 : Fin 2) ≠ 1) (by decide)

/-- Constant control code whose range is a singleton antichain, but not injective (`n = 2`). -/
private def duplicateCode : Fin 2 → Fin 2 → Bool :=
  fun _ => ![true, false]

-- Boundary check: `Set.range duplicateCode` is an antichain, yet injectivity fails so no monotone
-- circuit can compute `S_{1, duplicateCode}`.
example :
    IsAntichain (· ≤ ·) (Set.range duplicateCode) ∧
    ¬ ∃ c : Circuit signature (2 * 1 + 2) (2 * 1),
      ComputesMonotoneShift c duplicateCode := by
  refine ⟨?_, ?_⟩
  · have hrange : Set.range duplicateCode = {![true, false]} := by
      ext y
      simp [duplicateCode, eq_comm]
    rw [hrange]
    exact IsAntichain.singleton
  · rintro ⟨c, hc⟩
    have hinj := (hc.injective_and_isAntichain (by decide)).1
    have h01 : (0 : Fin 2) = 1 := hinj rfl
    exact absurd h01 (by decide)

-- Concrete lower- vs upper-bound sandwich at `n = 8, q = 2`:
-- every monotone shift circuit (over any control code `α : Fin 8 → Fin m → Bool`) and every
-- monotone permutation circuit (over any `β : Equiv.Perm (Fin 8) → Fin m → Bool`) has binary gate
-- cost at least `2 * ∑_{t=1}^8 ⌈log₂ t⌉ = 34` (and `q n log₂ n - q n = 32`), while
-- `dualRailShiftCircuit 8 2 3 (by decide)` achieves `144` gates.
example {m : ℕ} {α : Fin 8 → Fin m → Bool} {β : Equiv.Perm (Fin 8) → Fin m → Bool}
    {cS cP : Circuit signature (8 * 2 + m) (8 * 2)}
    (hcS : ComputesMonotoneShift cS α) (hcP : ComputesMonotonePerm cP β) :
    34 ≤ cS.program.cost binaryCost ∧
    32 ≤ cS.program.cost binaryCost ∧
    34 ≤ cP.program.cost binaryCost ∧
    32 ≤ cP.program.cost binaryCost ∧
    (dualRailShiftCircuit 8 2 3 (by decide)).program.cost binaryCost = 144 := by
  have hsum : 2 * (∑ t ∈ Icc 1 8, Nat.clog 2 t) = 34 := by decide
  have hlog : 2 * 8 * Nat.log 2 8 - 2 * 8 = 32 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hsum ▸ mul_sum_clog_le_cost_of_computesMonotoneShift hcS
  · exact hlog ▸ mul_log_sub_le_cost_of_computesMonotoneShift hcS
  · exact hsum ▸ mul_sum_clog_le_cost_of_computesMonotonePerm hcP
  · exact hlog ▸ mul_log_sub_le_cost_of_computesMonotonePerm hcP
  · rw [cost_dualRailShiftCircuit]; decide

end CslibFrontierTests.MonotoneShift
