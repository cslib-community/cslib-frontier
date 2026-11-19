/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.AlmostSynchronousReduction

/-! # Projective spectral rounding for a strategy with unequal local dimensions -/

set_option linter.privateModule false

open Cslib.PCP Cslib.Quantum Matrix

private noncomputable def rectangular : QuantumStrategy Unit Unit Bool Bool Bool Unit where
  state := EuclideanSpace.single (false, ()) 1
  norm_state := by simp
  alice _ := POVM.const false
  bob _ := POVM.const true

/-- The two conclusions recover reduced states on different native index types. -/
example :
    (∃ (d : Bool → ℝ) (U : Matrix Bool Bool ℂ),
      partialTraceRight (pureState rectangular.state) =
        ∑ s : {s : Finset Bool // s.Nonempty}, QuantumStrategy.spectralCutWeight d s •
          (U * QuantumStrategy.spectralCutDensity s * Uᴴ)) ∧
    (∃ (d : Unit → ℝ) (U : Matrix Unit Unit ℂ),
      partialTraceLeft (pureState rectangular.state) =
        ∑ s : {s : Finset Unit // s.Nonempty}, QuantumStrategy.spectralCutWeight d s •
          (U * QuantumStrategy.spectralCutDensity s * Uᴴ)) := by
  let ν := PMF.pure ()
  obtain ⟨d₁, U₁, _, h₁⟩ := rectangular.exists_alice_projective_spectral_mixture
  obtain ⟨_, _, _, _, _, _, _, _, h₁', _⟩ := h₁ ν
  obtain ⟨d₂, U₂, _, h₂⟩ := rectangular.exists_bob_projective_spectral_mixture
  obtain ⟨_, _, _, _, _, _, _, _, h₂', _⟩ := h₂ ν
  exact ⟨⟨d₁, U₁, h₁'⟩, ⟨d₂, U₂, h₂'⟩⟩
