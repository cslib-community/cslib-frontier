/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.PhaseCode
public import CslibFrontier.Computability.Circuit.Quantum.Parallel
public import CslibFrontier.Foundations.Quantum.DensityMatrix.Product
public import CslibFrontier.Foundations.Quantum.POVM.Density

/-!
# Uniform verifiers with independent mixed-state proofs

The proof registers are consecutive blocks after the classical input. All registers
outside those blocks are in their specified computational basis state. The joint
input is the tensor product of the independent proof density matrices and that
basis state, relabeled to the verifier's wire order.

## Main definitions

* `Cslib.Quantum.UniformQuantifiedVerifier`: a uniform circuit and proof layout.
* `Cslib.Quantum.UniformQuantifiedVerifier.inputDensity`: the joint initial state.
* `Cslib.Quantum.UniformQuantifiedVerifier.acceptProb`: unitary evolution and basis readout.
-/

public section

namespace Cslib.Quantum

open scoped Kronecker
open Turing.MultiTapeTM

/-- A mixed proof of `p` qubits is a density operator on its computational basis. -/
abbrev MixedProof (p : ℕ) := {ρ : Matrix (Fin p → Bool) (Fin p → Bool) ℂ // IsDensityMatrix ρ}

/-- A uniform verifier with `k` consecutive equal-width proof registers after the input. -/
structure UniformQuantifiedVerifier (k : ℕ) extends UniformPhaseCircuitFamily where
  /-- Each proof register's separately computed width. -/
  proofWidth : ℕ → ℕ
  computableInPolyTime_proofWidth : ComputableInPolyTime proofWidth encUnary encUnary
  add_proofWidth_le : ∀ n, n + k * proofWidth n ≤ width n

namespace UniformQuantifiedVerifier

variable {k : ℕ} (V : UniformQuantifiedVerifier k)

/-- The combined proof block as an embedding into the verifier's wires. -/
@[expose] def proofWires (n : ℕ) : Fin (k * V.proofWidth n) ↪ Fin (V.width n) :=
  blockEmb n (V.add_proofWidth_le n)

private def splitProofs (n : ℕ) :
    (Fin (k * V.proofWidth n) → Bool) ≃ (Fin k → Fin (V.proofWidth n) → Bool) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.curry _ _ _)

/-- Prepare the independent proof registers, the encoded input, and zero workspace. -/
noncomputable def inputDensity (x : List Bool)
    (states : Fin k → MixedProof (V.proofWidth x.length)) :
    Matrix (Fin (V.width x.length) → Bool) (Fin (V.width x.length) → Bool) ℂ :=
  let e := V.proofWires x.length
  let proofBasis := V.splitProofs x.length
  let jointProof := (productDensity fun i => (states i).val).submatrix proofBasis proofBasis
  let fixedBits := fun j : {j // ¬∃ i, e i = j} => inputState (V.width x.length) x j.val
  (jointProof ⊗ₖ pureState (ket fixedBits)).submatrix (splitEquiv e) (splitEquiv e)

/-- Product-state initialization preserves positivity and total trace. -/
theorem isDensityMatrix_inputDensity (x : List Bool)
    (states : Fin k → MixedProof (V.proofWidth x.length)) :
    IsDensityMatrix (V.inputDensity x states) := by
  have hproof := isDensityMatrix_productDensity (fun i => (states i).val)
    (fun i => (states i).property)
  exact ((hproof.submatrix_equiv (V.splitProofs x.length)).kronecker
    (isDensityMatrix_pureState (norm_ket _))).submatrix_equiv (splitEquiv (V.proofWires x.length))

/-- Evolve the joint density matrix and sum the basis probabilities on accepting outcomes. -/
noncomputable def acceptProb (x : List Bool) (states : Fin k → MixedProof (V.proofWidth x.length)) :
    ℝ :=
  let U := (Circuit.ofPhaseCodes (V.width x.length) (V.gates x.length)).matrix
  let final := densityConj U.val (V.inputDensity x states)
  ∑ y ∈ accepting (V.width x.length), POVM.basis.densityProb final y

/-- The sum of the accepting basis probabilities is at most one. -/
theorem acceptProb_le_one (x : List Bool) (states : Fin k → MixedProof (V.proofWidth x.length)) :
    V.acceptProb x states ≤ 1 := by
  let U := (Circuit.ofPhaseCodes (V.width x.length) (V.gates x.length)).matrix
  let final := densityConj U.val (V.inputDensity x states)
  have hfinal : IsDensityMatrix final := by
    dsimp only [final]
    rw [densityConj_apply]
    exact (V.isDensityMatrix_inputDensity x states).conj_unitary U.property
  change (∑ y ∈ accepting (V.width x.length), POVM.basis.densityProb final y) ≤ 1
  calc
    _ ≤ ∑ y, POVM.basis.densityProb final y :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun y _ _ =>
        POVM.basis.densityProb_nonneg hfinal.posSemidef y
    _ = 1 := by rw [POVM.sum_densityProb, hfinal.trace_eq_one, Complex.one_re]

end UniformQuantifiedVerifier
end Cslib.Quantum
