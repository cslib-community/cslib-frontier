/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.Quantum
import CslibFrontier.Foundations.Quantum.Bipartite
import CslibFrontier.Probability.PMF.Map

/-!
# Independent tensor strategies

Two strategies can be played independently with the product of their shared states. Each
player measures their two local registers with the product of their two local POVMs.
For fixed questions, the answer pairs have the independent product law, with the
coordinates grouped by player.
-/

public section

namespace Cslib.PCP.QuantumStrategy

open Cslib.Quantum Matrix
open scoped Kronecker

variable {X Y A B X' Y' A' B' ι κ ι' κ' : Type*}
  [Fintype A] [Fintype B] [Fintype A'] [Fintype B']
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype ι'] [DecidableEq ι'] [Fintype κ'] [DecidableEq κ']

variable (S : QuantumStrategy X Y A B ι κ) (T : QuantumStrategy X' Y' A' B' ι' κ')

/-- Play both strategies on separate registers, with the questions, answers and registers
grouped by player. -/
noncomputable def tensor :
    QuantumStrategy (X × X') (Y × Y') (A × A') (B × B') (ι × ι') (κ × κ') where
  state := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (Equiv.prodProdProdComm ι ι' κ κ').symm (prodState S.state T.state)
  norm_state := by
    rw [LinearIsometryEquiv.norm_map, norm_prodState, S.norm_state, T.norm_state, one_mul]
  alice x := (S.alice x.1).kronecker (T.alice x.2)
  bob y := (S.bob y.1).kronecker (T.bob y.2)

/-- The Born probability of a pair of independent outcomes is the product of their probabilities. -/
theorem prob_tensor (x : X × X') (y : Y × Y') (a : A × A') (b : B × B') :
    (S.tensor T).prob x y a b = S.prob x.1 y.1 a.1 b.1 * T.prob x.2 y.2 a.2 b.2 := by
  let L := (S.alice x.1).effect a.1 ⊗ₖ (S.bob y.1).effect b.1
  let R := (T.alice x.2).effect a.2 ⊗ₖ (T.bob y.2).effect b.2
  let e := Equiv.prodProdProdComm ι ι' κ κ'
  have hM : (((S.tensor T).alice x).effect a ⊗ₖ ((S.tensor T).bob y).effect b) =
      (L ⊗ₖ R).submatrix e e := by
    ext ⟨⟨i, i'⟩, ⟨j, j'⟩⟩ ⟨⟨k, k'⟩, ⟨l, l'⟩⟩
    simp only [tensor, POVM.kronecker, L, R, e, Matrix.kronecker_apply, Matrix.submatrix_apply,
      Equiv.prodProdProdComm_apply]
    ac_rfl
  apply Complex.ofReal_injective
  simp only [QuantumStrategy.prob, Complex.ofReal_mul, POVM.ofReal_prob, POVM.kronecker]
  rw [hM]
  change star ((prodState S.state T.state).ofLp ∘ e) ⬝ᵥ
      ((L ⊗ₖ R).submatrix e e *ᵥ ((prodState S.state T.state).ofLp ∘ e)) =
    (star S.state.ofLp ⬝ᵥ (L *ᵥ S.state.ofLp)) *
      (star T.state.ofLp ⬝ᵥ (R *ᵥ T.state.ofLp))
  have hreindex := star_dotProduct_submatrix_mulVec e.symm (L ⊗ₖ R)
    (prodState S.state T.state).ofLp
  rw [Equiv.symm_symm] at hreindex
  rw [hreindex, kronecker_mulVec_prodState]
  let ψ : EuclideanSpace ℂ (ι × κ) := WithLp.toLp 2 (L *ᵥ S.state.ofLp)
  let φ : EuclideanSpace ℂ (ι' × κ') := WithLp.toLp 2 (R *ᵥ T.state.ofLp)
  rw [← funext (prodState_apply ψ φ)]
  change (star (prodState S.state T.state).ofLp ⬝ᵥ (prodState ψ φ).ofLp) =
    (star S.state.ofLp ⬝ᵥ ψ.ofLp) * (star T.state.ofLp ⬝ᵥ φ.ofLp)
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using
    inner_prodState S.state ψ T.state φ

/-- Independently sample both answer pairs, then regroup the answers by player. -/
theorem answers_tensor (x : X × X') (y : Y × Y') :
    (S.tensor T).answers x y =
      ((S.answers x.1 y.1).bind fun ab => (T.answers x.2 y.2).map (ab, ·)).map
        (Equiv.prodProdProdComm A B A' B') := by
  ext ⟨⟨a, a'⟩, ⟨b, b'⟩⟩
  rw [Probability.PMF.map_equiv_apply, Probability.PMF.bind_map_prodMk_apply]
  simp only [answers, POVM.measure_apply]
  change ENNReal.ofReal ((S.tensor T).prob x y (a, a') (b, b')) =
    ENNReal.ofReal (S.prob x.1 y.1 a b) * ENNReal.ofReal (T.prob x.2 y.2 a' b')
  rw [prob_tensor, ENNReal.ofReal_mul (S.prob_nonneg _ _ _ _)]

end Cslib.PCP.QuantumStrategy
