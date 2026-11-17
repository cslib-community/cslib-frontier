/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.MagicSquare
public import CslibFrontier.Computability.PCP.TwoProverGame.Tsirelson
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# The commuting-operator value

The **commuting-operator value** `ω_qc(G)` of a two-prover game
(`Cslib.PCP.TwoProverGame.commutingValue`) is the supremum of the winning probability of
commuting-operator strategies (`Cslib.PCP.CommutingStrategy`) over all C⋆-algebras
(`Cslib.Quantum.CStarAlg`, a C⋆-algebra in `Type` with its order). By the GNS construction, which
is not used here, this is the value of the commuting-operator model of Tsirelson: commuting
measurements of the two provers on one Hilbert space
[Ji, Natarajan, Vidick, Wright and Yuen][JNVWY2020].

Every finite-dimensional tensor-product strategy is a commuting-operator strategy in the C⋆-algebra
of matrices (`Cslib.PCP.QuantumStrategy.toCommuting`), so the values are ordered,

`ω(G) ≤ ω*(G) ≤ ω_qc(G) ≤ 1`

(`Cslib.PCP.TwoProverGame.value_le_quantumValue`,
`Cslib.PCP.TwoProverGame.quantumValue_le_commutingValue`). Whether the second inequality can be
strict for some game is Tsirelson's problem, answered positively through `MIP* = RE`; for CHSH and
the magic square both values agree: Tsirelson's bound holds in the commuting-operator model, so
`ω_qc(CHSH) = cos²(π/8)` (`Cslib.PCP.TwoProverGame.commutingValue_chsh`), and
`ω_qc(magic square) = 1` (`Cslib.PCP.TwoProverGame.commutingValue_magicSquare`).

## Main definitions

* `Cslib.Quantum.CStarAlg`: a C⋆-algebra in `Type`, with the order of its positive elements.
* `Cslib.PCP.TwoProverGame.commutingValue`: the commuting-operator value.

## Main results

* `Cslib.PCP.TwoProverGame.commutingWinProb_le_commutingValue`: every commuting-operator strategy
  in a C⋆-algebra is bounded by the value.
* `Cslib.PCP.TwoProverGame.quantumValue_le_commutingValue`: `ω* ≤ ω_qc`.
* `Cslib.PCP.TwoProverGame.commutingValue_chsh`: `ω_qc(CHSH) = cos²(π/8)`.
* `Cslib.PCP.TwoProverGame.commutingValue_magicSquare`: `ω_qc(magic square) = 1`.

## References

* [Z. Ji, A. Natarajan, T. Vidick, J. Wright and H. Yuen, *MIP* = RE*][JNVWY2020]
-/

@[expose] public section

namespace Cslib.Quantum

/-- A **C⋆-algebra** in `Type`, with the order of its positive elements: the algebras of
observables of the commuting-operator model. -/
structure CStarAlg where
  /-- The algebra. -/
  carrier : Type
  [cstar : CStarAlgebra carrier]
  [partialOrder : PartialOrder carrier]
  [starOrderedRing : StarOrderedRing carrier]

attribute [instance] CStarAlg.cstar CStarAlg.partialOrder CStarAlg.starOrderedRing

end Cslib.Quantum

namespace Cslib.PCP.TwoProverGame

open Quantum
open scoped Real

variable {X Y A B : Type} [Fintype A] [Fintype B] (G : TwoProverGame X Y A B)

/-- The **commuting-operator value** `ω_qc(G)`: the supremum of the winning probability of
commuting-operator strategies over all C⋆-algebras. -/
noncomputable def commutingValue : ℝ :=
  ⨆ (𝒜 : CStarAlg) (S : CommutingStrategy X Y A B 𝒜.carrier), G.commutingWinProb S

theorem commutingValue_nonneg : 0 ≤ G.commutingValue :=
  Real.iSup_nonneg fun _ => Real.iSup_nonneg fun S => G.commutingWinProb_nonneg S

/-- The commuting-operator value is at most `c` when every strategy wins with probability at most
`c`. -/
theorem commutingValue_le {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ (𝒜 : Type) [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
      (S : CommutingStrategy X Y A B 𝒜), G.commutingWinProb S ≤ c) :
    G.commutingValue ≤ c :=
  Real.iSup_le (fun 𝒜 => Real.iSup_le (fun S => h 𝒜.carrier S) hc) hc

theorem commutingValue_le_one : G.commutingValue ≤ 1 :=
  G.commutingValue_le zero_le_one fun _ _ _ _ S => G.commutingWinProb_le_one S

/-- Every commuting-operator strategy in a C⋆-algebra wins with probability at most the
commuting-operator value. -/
theorem commutingWinProb_le_commutingValue (𝒜 : Type) [CStarAlgebra 𝒜] [PartialOrder 𝒜]
    [StarOrderedRing 𝒜] (S : CommutingStrategy X Y A B 𝒜) :
    G.commutingWinProb S ≤ G.commutingValue := by
  have hb : ∀ 𝒜 : CStarAlg, BddAbove
      (Set.range fun S : CommutingStrategy X Y A B 𝒜.carrier => G.commutingWinProb S) :=
    fun 𝒜 => ⟨1, by rintro _ ⟨S, rfl⟩; exact G.commutingWinProb_le_one S⟩
  have hb' : BddAbove (Set.range fun 𝒜 : CStarAlg =>
      ⨆ S : CommutingStrategy X Y A B 𝒜.carrier, G.commutingWinProb S) :=
    ⟨1, by
      rintro _ ⟨𝒜, rfl⟩
      exact Real.iSup_le (fun S => G.commutingWinProb_le_one S) zero_le_one⟩
  exact (le_ciSup (hb ⟨𝒜⟩) S).trans (le_ciSup hb' ⟨𝒜⟩)

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder in
/-- A tensor-product strategy wins with probability at most the commuting-operator value. -/
theorem quantumWinProb_le_commutingValue {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (S : QuantumStrategy X Y A B ι κ) :
    G.quantumWinProb S ≤ G.commutingValue := by
  rw [← commutingWinProb_toCommuting]
  exact G.commutingWinProb_le_commutingValue (Matrix (ι × κ) (ι × κ) ℂ) S.toCommuting

/-- **The entangled value is at most the commuting-operator value**: `ω* ≤ ω_qc`. -/
theorem quantumValue_le_commutingValue : G.quantumValue ≤ G.commutingValue :=
  G.quantumValue_le G.commutingValue_nonneg fun S => G.quantumWinProb_le_commutingValue S

/-- The classical value is at most the commuting-operator value. -/
theorem value_le_commutingValue [Finite X] [Finite Y] [Nonempty A] [Nonempty B] :
    G.value ≤ G.commutingValue :=
  G.value_le_quantumValue.trans G.quantumValue_le_commutingValue

/-- **Tsirelson's bound in the commuting-operator model**: `ω_qc(CHSH) = cos²(π/8)`. -/
theorem commutingValue_chsh : chsh.commutingValue = Real.cos (π / 8) ^ 2 :=
  le_antisymm (chsh.commutingValue_le (sq_nonneg _) fun _ _ _ _ S => commutingWinProb_chsh_le S)
    (quantumValue_chsh ▸ chsh.quantumValue_le_commutingValue)

/-- The commuting-operator value of the magic square is `1`. -/
theorem commutingValue_magicSquare : magicSquare.commutingValue = 1 :=
  le_antisymm magicSquare.commutingValue_le_one
    (quantumValue_magicSquare ▸ magicSquare.quantumValue_le_commutingValue)

end Cslib.PCP.TwoProverGame
