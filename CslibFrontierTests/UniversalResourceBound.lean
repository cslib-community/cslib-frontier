/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.ResourceBound

/-! The universal resource estimates are available without importing complexity classes. -/

open Turing.MultiTapeTM.Universal

example {D N J B L : ℕ} (hD : D ≤ B) (hN : N ≤ B) (hL : L ≤ B) (hJ : 1 ≤ J) :
    (J + 1) * (stepBound D N J + runBound D N J + (L + 1) ^ 2) ≤
        100000 * (B + 1) ^ 4 * J ^ 2 ∧
      runBound D N J ≤ 200 * (B + 1) ^ 2 * J :=
  universal_bounds_le hD hN hL hJ

-- The minimum permitted clock and zero size bounds satisfy all hypotheses.
example : 2 * (stepBound 0 0 1 + runBound 0 0 1 + 1) ≤ 100000 ∧
    runBound 0 0 1 ≤ 200 := by
  simpa using universal_bounds_le (D := 0) (N := 0) (J := 1) (B := 0) (L := 0)
    (by decide) (by decide) (by decide) (by decide)

example {D N : ℕ} : runBound D N 0 ≤ runBound D N 1 := runBound_mono (by decide)

-- The improved plain theorem supplies one actual native machine for both a zero clock and
-- a one-step missing-transition halt, with the advertised finite resource bounds.
private def emptyDescription : Desc := ⟨0, 0, []⟩

attribute [local irreducible] eDesc in
example : ∃ (c k : ℕ) (State : Type) (_ : Finite State)
    (tm : Turing.MultiTapeTM k Bool State),
    tm.ComputesInTimeAndSpace (eIn (emptyDescription, [], 0)) (eOut ([], false))
      (c * 2402) (c * 50) ∧
    tm.ComputesInTimeAndSpace (eIn (emptyDescription, [], 1)) (eOut ([], true))
      (c * 16385) (c * 129) := by
  obtain ⟨c, ⟨k, State, hfinite, tm, htm⟩, _⟩ := computableInO_universal
  -- One common factor absorbs all four finite resource values; the test does not require
  -- the implementation's exact resource expressions to be definitionally small numerals.
  have budgets (t₀ s₀ t₁ s₁ c : ℕ) :
      c * t₀ ≤ (c * (t₀ + s₀ + t₁ + s₁)) * 2402 ∧
      c * s₀ ≤ (c * (t₀ + s₀ + t₁ + s₁)) * 50 ∧
      c * t₁ ≤ (c * (t₀ + s₀ + t₁ + s₁)) * 16385 ∧
      c * s₁ ≤ (c * (t₀ + s₀ + t₁ + s₁)) * 129 := by
    simp only [Nat.mul_add, Nat.add_mul]
    omega
  have ho0 : universal (emptyDescription, [], 0) = ([], false) := by decide +kernel
  have ho1 : universal (emptyDescription, [], 1) = ([], true) := by decide +kernel
  have h0 := htm (emptyDescription, [], 0)
  have h1 := htm (emptyDescription, [], 1)
  change tm.ComputesInTimeAndSpace _ _
    (c * (universalImplementationTime (emptyDescription, [], 0) + 1))
    (c * (universalImplementationSpace (emptyDescription, [], 0) + 1)) at h0
  change tm.ComputesInTimeAndSpace _ _
    (c * (universalImplementationTime (emptyDescription, [], 1) + 1))
    (c * (universalImplementationSpace (emptyDescription, [], 1) + 1)) at h1
  obtain ⟨ht0, hs0, ht1, hs1⟩ := budgets
    (universalImplementationTime (emptyDescription, [], 0) + 1)
    (universalImplementationSpace (emptyDescription, [], 0) + 1)
    (universalImplementationTime (emptyDescription, [], 1) + 1)
    (universalImplementationSpace (emptyDescription, [], 1) + 1) c
  rw [ho0] at h0
  rw [ho1] at h1
  exact ⟨_, k, State, hfinite, tm,
    ⟨h0.1, h0.2.1.mono ht0, h0.2.2.mono hs0⟩,
    ⟨h1.1, h1.2.1.mono ht1, h1.2.2.mono hs1⟩⟩
