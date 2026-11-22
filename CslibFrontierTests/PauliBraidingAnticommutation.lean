/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.PauliBraidingAnticommutation
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Order

/-! # CHSH extraction in the width-one Pauli braiding game -/

set_option linter.privateModule false

namespace CslibFrontierTests.PauliBraidingAnticommutation

open Cslib Cslib.PCP Cslib.Quantum Cslib.BitString Finset
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Real

private abbrev Strategy :=
  CommutingStrategy (PauliBraidingQuestion 1 Bool) (PauliBraidingQuestion 1 Bool)
    ((Bool × Bool) ⊕ Bool) ((Bool × Bool) ⊕ Bool) (Matrix Bool Bool ℂ)

private def odd : ↥(oddPairs (Fin 1)) :=
  ⟨(fun _ => true, fun _ => true), mem_oddPairs.mpr (by decide)⟩

private noncomputable def malformed (φ : AlgState (Matrix Bool Bool ℂ)) : Strategy where
  state := φ
  alice _ := Measurement.const (.inl (false, false))
  bob _ := Measurement.const (.inl (false, false))
  commute _ _ a b := by
    simp only [Measurement.const]
    split_ifs <;> simp [Commute, SemiconjBy]

/-- The bound uses the usual ordered scalar action on finite complex matrices. -/
example (S : Strategy) (roles : Bool) :
    let measure := cond roles S.bob S.alice
    let X (x : Fin 1 → Bool) := 𝔼 d, pauliBraidingBasisObservable measure false x d
    let Z (z : Fin 1 → Bool) := 𝔼 d, pauliBraidingBasisObservable measure true z d
    let branch := pauliBraidingBranchGame 1 TwoProverGame.chsh id (fun _ => id)
    S.state.norm (X odd.val.1 * Z odd.val.2 + Z odd.val.2 * X odd.val.1) ^ 2 ≤
      9 * (4096 * (1 - (branch 2).commutingWinProb S) +
        2 * chshAnticommConst * (Real.cos (π / 8) ^ 2 - (branch 1).commutingWinProb S)) := by
  have h := expect_norm_pauliBraidingBasis_anticomm_sq_le S roles
  let : Unique ↥(oddPairs (Fin 1)) := ⟨⟨odd⟩, fun p => by
    obtain ⟨⟨a, b⟩, hp⟩ := p
    have h := mem_oddPairs.mp hp
    have hbits : a 0 = true ∧ b 0 = true := by
      simpa [dotProduct, Fintype.sum_unique, Bool.mul_eq_and] using h
    apply Subtype.ext
    exact Prod.ext (funext fun i => Subsingleton.elim i (0 : Fin 1) ▸ hbits.1)
      (funext fun i => Subsingleton.elim i (0 : Fin 1) ▸ hbits.2)⟩
  dsimp only at h ⊢
  rwa [Fintype.expect_unique] at h

/-- Wrong-tag answers lose in the verifier. Postprocessing sends both to false, giving the
constant strategy's CHSH score in either role. -/
example (φ : AlgState (Matrix Bool Bool ℂ)) (roles : Bool) :
    (pauliBraidingCHSHGame 1 roles odd).commutingWinProb (malformed φ) = 0 ∧
      TwoProverGame.chsh.commutingWinProb
        (pauliBraidingCHSHStrategy (malformed φ) roles odd) = 3 / 4 := by
  classical
  constructor
  · rw [SeededGame.commutingWinProb_eq_sum]
    refine sum_eq_zero fun r _ => mul_eq_zero_of_right _ (sum_eq_zero fun a _ =>
      sum_eq_zero fun b _ => ?_)
    by_cases h : (pauliBraidingCHSHGame 1 roles odd).accepts r a b
    · have ha : a ≠ .inl (false, false) := by
        intro ha
        subst a
        cases roles <;> cases b <;> exact h
      simp [h, CommutingStrategy.prob, malformed, Measurement.const, ha]
    · simp [h]
  · have hprob (x y a b : Bool) :
        (pauliBraidingCHSHStrategy (malformed φ) roles odd).prob x y a b =
          if a = false ∧ b = false then 1 else 0 := by
      cases roles <;> cases a <;> cases b <;>
        simp [pauliBraidingCHSHStrategy, CommutingStrategy.swap, CommutingStrategy.map,
          CommutingStrategy.prob, malformed, Measurement.const, Measurement.map_effect,
          φ.map_one]
    rw [TwoProverGame.commutingWinProb_eq_sum]
    simp only [hprob, TwoProverGame.chsh_questions_apply, Fintype.sum_bool]
    norm_num [TwoProverGame.chsh]

end CslibFrontierTests.PauliBraidingAnticommutation
