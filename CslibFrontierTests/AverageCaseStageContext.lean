/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of MildlyHardOnAverageFor and LogSpaceDerandomization StageContext)

import CslibFrontier.Computability.Complexity.AverageCase
import CslibFrontier.Computability.LogSpaceDerandomization.NormalizedAtomRows.SecondEnvelope
import CslibFrontier.Computability.LogSpaceDerandomization.NormalizedAtomRows.RootReserveOutput
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Tests for `MildlyHardOnAverageFor` and `StageContext`

Checks positive and negative nonvacuity of the parametric `MildlyHardOnAverageFor` hardness kernel
across both `Eventually` and `Frequently` quantifiers, and provides concrete nonvacuous instances
of `CutoffProfile`, `BinSchedule`, `ResidualStage`, and `ReserveOutputContext` with a nonzero
stochastic kernel.
-/

set_option linter.privateModule false

noncomputable section

section AverageCaseKernelTests

open Filter Cslib Cslib.Complexity Cslib.Probability Turing.MultiTapeTM

-- Both `Eventually` and `Frequently` transport along eventual implications via `MonoQuant`.
example : (∃ᶠ n in atTop, 10 ≤ n + 1) ∧ (∀ᶠ n in atTop, 1 ≤ n + 1) := by
  have hev : ∀ᶠ n : ℕ in atTop, 10 ≤ n := eventually_ge_atTop 10
  exact ⟨MonoQuant.imp_of_eventually (Quant := (Filter.Frequently · atTop))
      (.of_forall fun n hn => by omega) hev.frequently,
    MonoQuant.imp_of_eventually (Quant := (Filter.Eventually · atTop))
      (.of_forall fun n _ => by omega) (eventually_ge_atTop 0)⟩

-- Positive nonvacuity of `MildlyHardOnAverageFor`: the constant-`⊤` function `List Bool → ℕ∞`
-- is mildly hard on average against all uniform strict PPT heuristics (success probability is 0).
example : MildlyHardOnAverageENat (fun _ => (⊤ : ℕ∞)) ∧
    MildlyHardOnAverageIOENat (fun _ => (⊤ : ℕ∞)) := by
  have htop : MildlyHardOnAverageENat (fun _ => (⊤ : ℕ∞)) := by
    refine ⟨1, fun _ => by simp, fun H _ => .of_forall fun n => ?_⟩
    have hzero : ((do
        let x ← BitString.uniformList n
        (ProbComp.eval (H x)).map fun v : ℕ => decide ((v : ℕ∞) = ⊤) : PMF Bool) true) = 0 := by
      simp
    rw [hzero]
    norm_num
  have hio : MildlyHardOnAverageIOENat (fun _ => (⊤ : ℕ∞)) :=
    (MildlyHardOnAverageWith.mildlyHardOnAverageDetWith htop).mildlyHardOnAverageIOWith
  exact ⟨htop, hio⟩

-- Negative nonvacuity of `MildlyHardOnAverageFor`: any constant `ℕ` function is easy against
-- deterministic polynomial-time heuristics, so even infinitely-often hardness fails.
example : ¬ MildlyHardOnAverageIO (fun _ => 7) ∧ ¬ MildlyHardOnAverage (fun _ => 7) := by
  have hio : ¬ MildlyHardOnAverageIO (fun _ => 7) :=
    MildlyHardOnAverageFor.not_of_admissible_pure (Quant := (Filter.Frequently · atTop))
      (Admissible := IsDetPolyTime encNat) (correct := fun _ _ v => decide (v = 7))
      (fun h => nomatch h.exists)
      (IsDetPolyTime.of_computableInPolyTime (ComputableInPolyTime.const 7))
      (.of_forall fun _ _ _ => rfl)
  exact ⟨hio, fun h => hio h.mildlyHardOnAverageIO⟩

-- Zero-gap equivalence and `2g → g` shifting specialize cleanly on both PPT and Det predicates.
example (f : List Bool → ℕ) :
    (MildlyHardOnAverageToApprox (fun _ => 0) f ↔ MildlyHardOnAverage f) ∧
      (MildlyHardOnAverageToOneSidedApproxIO (fun _ => 0) f ↔ MildlyHardOnAverageIO f) := by
  simp only [MildlyHardOnAverageToApprox, MildlyHardOnAverage,
    MildlyHardOnAverageToOneSidedApproxIO, MildlyHardOnAverageIO]
  exact ⟨MildlyHardOnAverageFor.approx_zero_iff, MildlyHardOnAverageFor.oneSidedApprox_zero_iff⟩

example (f : List Bool → ℕ)
    (h : MildlyHardOnAverageToOneSidedApprox (fun _ => 2 * 3) f) :
    MildlyHardOnAverageToApprox (fun _ => 3) f ∧
      MildlyHardOnAverageToApproxDet (fun _ => 3) f := by
  have happ : MildlyHardOnAverageToApprox (fun _ => 3) f :=
    h.mildlyHardOnAverageToApprox (ComputableInPolyTime.const 3)
  exact ⟨happ, happ.mildlyHardOnAverageToApproxDet⟩

end AverageCaseKernelTests

section StageContextTests

open Finset Cslib Cslib.Probability Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment
open Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open scoped BigOperators
attribute [local instance] Classical.propDecidable
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

-- Concrete `CutoffProfile.explicit` evaluates to exact 0/1 plateaus and rank 66.
example : CutoffProfile.explicit.binCutoff 0 = 0 ∧
    CutoffProfile.explicit.binCutoff (1 / 2) = 0 ∧
    CutoffProfile.explicit.binCutoff 1 = 1 ∧
    CutoffProfile.explicit.requestGate (1 / 2) = 1 ∧
    CutoffProfile.explicit.requestRank = 66 :=
  ⟨CutoffProfile.explicit.cutoff_zero 0 (by norm_num),
    CutoffProfile.explicit.cutoff_zero (1 / 2) le_rfl,
    CutoffProfile.explicit.cutoff_one 1 le_rfl,
    CutoffProfile.explicit.gate_one (1 / 2) (by dsimp only [CutoffProfile.explicit]; norm_num),
    rfl⟩

-- Concrete `BinSchedule.step` has strictly decreasing rates with exact adjacent ratio 16,
-- while keeping bounded routed cutoffs inside `[0, cap i]` and `[0, max densityCap 16]`.
example :
    let b := BinSchedule.step 2 1 (cap := 3) (by norm_num)
    #b.activeBins = 3 ∧
      b.rates 1 < b.rates 0 ∧
      b.rates 0 / b.rates 1 = 16 ∧
      b.bounded CutoffProfile.explicit 0 100 ∈ Set.Icc 0 3 ∧
      b.bounded CutoffProfile.explicit 1 100 ∈ Set.Icc 0 16 := by
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩
  · norm_num [BinSchedule.rates, BinSchedule.step, rate]
  · norm_num [BinSchedule.rates, BinSchedule.step, rate]
  · simpa only [BinSchedule.cap, BinSchedule.step, estimatedBinCap, ↓reduceIte] using
      (BinSchedule.step 2 1 (cap := 3) (by norm_num)).bounded_grid_range
        CutoffProfile.explicit 0 100
  · simpa only [BinSchedule.cap, BinSchedule.step, estimatedBinCap, one_ne_zero, ↓reduceIte] using
      (BinSchedule.step 2 1 (cap := 3) (by norm_num)).bounded_grid_range
        CutoffProfile.explicit 1 100

private def stageRoles : RoleProfile 4 := ⟨0, 1, 2, by decide, by decide, by decide⟩

-- Nonzero stochastic kernel supported on column 0 with entry `1 = rate 0`:
-- every row sums to `1`, entries are in `{0, 1}`, and `BinSchedule.const 1 0 (cap := 1)` covers it.
private def nonzeroKernel : Matrix (ZMod 5) (ZMod 5) ℝ :=
  fun _ y => if y = 0 then 1 else 0

private def sampleStage (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ResidualStage HP 5 4 where
  direction := 1
  direction_ne_zero := by decide
  horizon := ⟨0, 4, by decide, by decide⟩
  roles := stageRoles
  level := 0
  sourceExponent := 0
  midpointExponent := 0
  terminalExponent := 0
  source_in_horizon := le_rfl
  midpoint_le_source := le_rfl
  sourceSuffix := [1]
  midpointSuffix := [2, 3]
  terminalSuffix := [4]
  cutoffs := CutoffProfile.explicit
  bins := BinSchedule.const 1 0 (cap := 1) (by norm_num)
  bins_in_horizon := by intros; exact le_rfl
  preparation_one := by intros; rfl
  kernel := nonzeroKernel
  kernel_nonneg := by
    intro x y
    unfold nonzeroKernel
    split_ifs <;> norm_num
  kernel_row_mass := by
    intro x
    simp [nonzeroKernel, Matrix.mulVec, dotProduct]
  kernel_rate := by
    intro x y
    unfold nonzeroKernel
    split_ifs <;> norm_num [rate]
  kernel_cap := by
    intro z w
    unfold nonzeroKernel
    simp only [BinSchedule.const]
    split_ifs <;> norm_num [rate]
  kernel_cover := by
    intro z y
    unfold nonzeroKernel
    split_ifs
    · right
      norm_num [BinSchedule.const, rate]
    · exact Or.inl rfl
  correctionRank := 6

private def zeroChildren (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ReserveOutputChildren HP 5 4 where
  raw _ _ _ _ _ _ := 0
  prep _ _ _ _ _ _ := 1
  maximum _ _ _ _ _ := 0

-- Nonvacuous `ResidualStage` check: the kernel has a strictly positive entry, active bins = 2,
-- `errorCalls` is nonempty, and the stage mean and moment bounds apply directly.
example : ∃ (HP : FourthRootHierarchyParams 16 1 16 32 8),
    let s := sampleStage HP
    s.kernel 0 0 = 1 ∧
      #s.bins.activeBins = 2 ∧
      1 ≤ #s.errorCalls ∧
      rowNormPow 4 5 (rate s.sourceExponent) s.sourceMask s.terminalMask
        (s.input (zeroChildren HP) 1) ≤ s.payment ∧
      |rowSliceMean s.sourceMask s.terminalMask (s.input (zeroChildren HP) 1) 0 0 -
        s.residual 0 0| ≤ s.cost (zeroChildren HP) 0 0 0 := by
  obtain ⟨HP⟩ := FourthRootHierarchyParams.nonempty
    (by norm_num : (0 : ℝ) < 16) (by norm_num : (0 : ℝ) < 1)
  let s := sampleStage HP
  have hk : s.kernel 0 0 = 1 := by simp [s, sampleStage, nonzeroKernel]
  have hcalls : (0, ⟨HierarchyTask.correctionAtomTask s.level false (Fin.last HP.k), s.source,
      {s.terminal with rate := s.midpoint.rate},
      {s.terminal with rate := min s.terminal.rate s.midpoint.rate}⟩) ∈ s.errorCalls := by
    simp [ResidualStage.errorCalls, HierarchyTask.residualErrorCalls]
  exact ⟨HP, hk, rfl, Finset.card_pos.mpr ⟨_, hcalls⟩,
    s.input_moment_le (zeroChildren HP) 1,
    s.mean_sub_le (zeroChildren HP) 0 0 0⟩

end StageContextTests
