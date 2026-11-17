/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.Quantum
public import CslibFrontier.Foundations.Quantum.Naimark

/-!
# Projective strategies suffice

Every tensor-product strategy has a **projective** strategy with the same answer distribution
(`Cslib.PCP.QuantumStrategy.dilate`, `Cslib.PCP.QuantumStrategy.answers_dilate`): each player
replaces each measurement by its Naimark dilation (`Cslib.Quantum.POVM.dilate`) on an ancilla
`ℂ^A` (respectively `ℂ^B`) prepared in a fixed state `|a₀⟩` (respectively `|b₀⟩`), and the shared
state `ψ` by `ψ ⊗ |a₀⟩ ⊗ |b₀⟩`. Because `Jᴴ P_a J = E_a` for the embedding `J ψ = ψ ⊗ |a₀⟩`, the
correlations `⟨ψ'|P_a ⊗ Q_b|ψ'⟩ = ⟨ψ|E_a ⊗ F_b|ψ⟩` are unchanged. Hence the entangled value is a
supremum over projective strategies (`Cslib.PCP.TwoProverGame.quantumWinProb_dilate`), and
theorems stated for projective strategies apply to every strategy.

## Main definitions

* `Cslib.PCP.QuantumStrategy.dilate`: the Naimark dilation of a strategy.

## Main results

* `Cslib.PCP.QuantumStrategy.answers_dilate`: the dilation has the same answer distribution.
* `Cslib.PCP.QuantumStrategy.isProjective_alice_dilate`,
  `Cslib.PCP.QuantumStrategy.isProjective_bob_dilate`: its measurements are projective.
* `Cslib.PCP.TwoProverGame.quantumWinProb_dilate`: it wins with the same probability.
-/

@[expose] public section

namespace Cslib.PCP

open Matrix Quantum
open scoped Kronecker MatrixOrder ComplexOrder

namespace QuantumStrategy

variable {X Y A B ι κ : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The embedding `ψ ↦ ψ ⊗ |a₀⟩ ⊗ |b₀⟩` of the shared state. -/
def dilateEmbed (a₀ : A) (b₀ : B) : Matrix ((ι × A) × (κ × B)) (ι × κ) ℂ :=
  ancillaEmbed a₀ ⊗ₖ ancillaEmbed b₀

theorem conjTranspose_dilateEmbed_mul (a₀ : A) (b₀ : B) :
    (dilateEmbed (ι := ι) (κ := κ) a₀ b₀)ᴴ * dilateEmbed (ι := ι) (κ := κ) a₀ b₀ = 1 := by
  rw [dilateEmbed, conjTranspose_kronecker, ← mul_kronecker_mul, conjTranspose_ancillaEmbed_mul,
    conjTranspose_ancillaEmbed_mul, one_kronecker_one]

/-- The **Naimark dilation** of a strategy: each measurement is replaced by its projective
dilation, and the shared state by `ψ ⊗ |a₀⟩ ⊗ |b₀⟩`. -/
noncomputable def dilate (S : QuantumStrategy X Y A B ι κ) (a₀ : A) (b₀ : B) :
    QuantumStrategy X Y A B (ι × A) (κ × B) where
  state := WithLp.toLp 2 (dilateEmbed a₀ b₀ *ᵥ S.state.ofLp)
  norm_state := by
    rw [Quantum.norm_toLp_mulVec_of_conjTranspose_mul_self
      (conjTranspose_dilateEmbed_mul a₀ b₀),
      S.norm_state]
  alice x := (S.alice x).dilate a₀
  bob y := (S.bob y).dilate b₀

theorem isProjective_alice_dilate (S : QuantumStrategy X Y A B ι κ) (a₀ : A) (b₀ : B) (x : X) :
    ((S.dilate a₀ b₀).alice x).toMeasurement.IsProjective :=
  (S.alice x).isProjective_dilate a₀

theorem isProjective_bob_dilate (S : QuantumStrategy X Y A B ι κ) (a₀ : A) (b₀ : B) (y : Y) :
    ((S.dilate a₀ b₀).bob y).toMeasurement.IsProjective :=
  (S.bob y).isProjective_dilate b₀

/-- The dilation has the same correlations. -/
theorem prob_dilate (S : QuantumStrategy X Y A B ι κ) (a₀ : A) (b₀ : B) (x : X) (y : Y) (a : A)
    (b : B) : (S.dilate a₀ b₀).prob x y a b = S.prob x y a b := by
  rw [prob_eq, prob_eq]
  change (star (dilateEmbed a₀ b₀ *ᵥ S.state.ofLp) ⬝ᵥ
    ((((S.alice x).dilate a₀).effect a ⊗ₖ ((S.bob y).dilate b₀).effect b) *ᵥ
      (dilateEmbed a₀ b₀ *ᵥ S.state.ofLp))).re = _
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, dilateEmbed,
    conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul,
    POVM.compress_dilate, POVM.compress_dilate]

/-- **The dilation has the same answer distribution.** -/
theorem answers_dilate (S : QuantumStrategy X Y A B ι κ) (a₀ : A) (b₀ : B) (x : X) (y : Y) :
    (S.dilate a₀ b₀).answers x y = S.answers x y := by
  ext ⟨a, b⟩
  rw [answers_apply, answers_apply, ← prob_eq, ← prob_eq, prob_dilate]

end QuantumStrategy

namespace TwoProverGame

variable {X Y A B ι κ : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (G : TwoProverGame X Y A B)

/-- The dilation of a strategy wins with the same probability. -/
theorem quantumWinProb_dilate (S : QuantumStrategy X Y A B ι κ) (a₀ : A) (b₀ : B) :
    G.quantumWinProb (S.dilate a₀ b₀) = G.quantumWinProb S := by
  rw [quantumWinProb, quantumWinProb]
  congr 1
  funext x y
  exact S.answers_dilate a₀ b₀ x y

end TwoProverGame

end Cslib.PCP
