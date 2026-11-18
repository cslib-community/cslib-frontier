/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Kolmogorov.UniversalMachine

/-! Checked clients of Goldreich's Theorem 1.10 (complexity with respect to a universal machine),
`Turing.MultiTapeTM.IsUniversal.exists_ecomplexity_le`. Applied to a machine computing the
identity it gives the first fact listed after the theorem in the December 2006 draft:
`K(s) ≤ |s| + O(1)`. -/

set_option linter.privateModule false

namespace CslibFrontierTests.GoldreichKolmogorov

open Turing MultiTapeTM Cslib.Kolmogorov DescriptionMethod

/-- `K_U(s) ≤ |s| + O(1)` for every universal machine `U` (Goldreich, the first fact after
Theorem 1.10): apply the theorem to a machine computing the identity. -/
example {k : ℕ} {S : Type*} {U : MultiTapeTM k Bool S} (hU : U.IsUniversal) :
    ∃ c : ℕ, ∀ s : List Bool, (ofMultiTapeTM U).ecomplexity s ≤ s.length + c := by
  obtain ⟨_, _, _, M, ⟨L⟩⟩ := exists_simulation_literal
  obtain ⟨c, hc⟩ := hU.exists_ecomplexity_le M
  refine ⟨c, fun s => (hc s).trans ?_⟩
  have hM : (ofMultiTapeTM M).ecomplexity s ≤ s.length := by
    simpa [ecomplexity_literal] using L.ecomplexity_le s
  gcongr

/-- Two universal machines give complexities within an additive constant of each other. -/
example {k₁ k₂ : ℕ} {S₁ S₂ : Type} [Finite S₁] [Finite S₂] {U₁ : MultiTapeTM k₁ Bool S₁}
    {U₂ : MultiTapeTM k₂ Bool S₂} (hU₁ : U₁.IsUniversal) (hU₂ : U₂.IsUniversal) :
    ∃ c : ℕ, ∀ s : List Bool,
      (ofMultiTapeTM U₁).ecomplexity s ≤ (ofMultiTapeTM U₂).ecomplexity s + c ∧
        (ofMultiTapeTM U₂).ecomplexity s ≤ (ofMultiTapeTM U₁).ecomplexity s + c := by
  obtain ⟨c₁, h₁⟩ := hU₁.exists_ecomplexity_le U₂
  obtain ⟨c₂, h₂⟩ := hU₂.exists_ecomplexity_le U₁
  refine ⟨max c₁ c₂, fun s => ⟨(h₁ s).trans ?_, (h₂ s).trans ?_⟩⟩ <;> gcongr
  exacts [le_max_left _ _, le_max_right _ _]

end CslibFrontierTests.GoldreichKolmogorov
