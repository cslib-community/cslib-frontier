/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Protocols.Quantum.OneTimePad
import CslibFrontier.Foundations.Quantum.Bell
import CslibFrontier.Foundations.Quantum.DensityMatrix.FidelityTraceDistance
import CslibFrontier.Foundations.Quantum.DensityMatrix.ClassicalQuantumInformationChain
import CslibFrontier.Foundations.Quantum.Pauli

/-! Density matrices, the partial trace, no-signalling and the quantum one-time pad: concrete
instances and edge cases. -/

namespace CslibFrontierTests.QuantumDensity

open Cslib.Quantum Cslib.Crypto.Protocols.Quantum.OneTimePad Matrix Finset
open scoped Kronecker MatrixOrder

/-! ### Density matrices -/

-- A basis state is a density matrix.
example : IsDensityMatrix (pureState (ket true)) := isDensityMatrix_pureState (norm_ket true)

-- The trace-one condition is not vacuous: `|0⟩⟨0| + |1⟩⟨1|` is positive semidefinite but has
-- trace two.
example : ¬ IsDensityMatrix (pureState (ket false) + pureState (ket true)) := by
  intro h
  have h1 := h.trace_eq_one
  rw [trace_add, trace_pureState, trace_pureState, norm_ket, norm_ket] at h1
  norm_num at h1

-- Bob's half of an EPR pair is the maximally mixed qubit `1 / 2`; so is Alice's.
example : partialTraceLeft (pureState bell) = (2 : ℂ)⁻¹ • (1 : Matrix Bool Bool ℂ) := by
  rw [bell, partialTraceLeft_pureState_maxEntangled, Fintype.card_bool, Nat.cast_ofNat]

example : partialTraceRight (pureState bell) = (2 : ℂ)⁻¹ • (1 : Matrix Bool Bool ℂ) := by
  rw [bell, partialTraceRight_pureState_maxEntangled, Fintype.card_bool, Nat.cast_ofNat]

/-! ### No-signalling -/

-- Whatever unitary Alice applies to her half of an EPR pair, Bob's half stays `1 / 2`.
example {U : Matrix Bool Bool ℂ} (hU : U ∈ unitaryGroup Bool ℂ) :
    partialTraceLeft ((U ⊗ₖ (1 : Matrix Bool Bool ℂ)) * pureState bell *
      (U ⊗ₖ (1 : Matrix Bool Bool ℂ))ᴴ) = (2 : ℂ)⁻¹ • (1 : Matrix Bool Bool ℂ) := by
  rw [partialTraceLeft_conj_unitary hU, bell, partialTraceLeft_pureState_maxEntangled,
    Fintype.card_bool, Nat.cast_ofNat]

-- The same holds if Alice measures her half and discards the outcome.
example : partialTraceLeft (∑ i, (single i i (1 : ℂ) ⊗ₖ (1 : Matrix Bool Bool ℂ)) * pureState bell *
      (single i i (1 : ℂ) ⊗ₖ (1 : Matrix Bool Bool ℂ))ᴴ) =
      (2 : ℂ)⁻¹ • (1 : Matrix Bool Bool ℂ) := by
  rw [partialTraceLeft_measure, bell, partialTraceLeft_pureState_maxEntangled, Fintype.card_bool,
    Nat.cast_ofNat]

/-! ### Pauli strings -/

-- On one qubit, `X^1` and `Z^1` are the Pauli matrices `X` and `Z`.
example : (pauliXPow (fun _ : Unit => true)).submatrix (Equiv.funUnique Unit Bool).symm
    (Equiv.funUnique Unit Bool).symm = pauliX := by
  ext b c
  cases b <;> cases c <;> simp [pauliXPow_apply, funext_iff]

example : (pauliZPow (fun _ : Unit => true)).submatrix (Equiv.funUnique Unit Bool).symm
    (Equiv.funUnique Unit Bool).symm = pauliZ := by
  ext b c
  cases b <;> cases c <;>
    simp [pauliZPow_apply, funext_iff, dotProduct, show (true * true : Bool) = true from rfl,
      show (true * false : Bool) = false from rfl]

/-! ### The quantum one-time pad -/

/-- Encrypting a basis state `|z⟩` with the key `(a, b)` gives the basis state `|z + a⟩`: the phase
flip only contributes a global sign. -/
theorem encrypt_pureState_ket {ι : Type*} [Fintype ι] [DecidableEq ι] (a b z : ι → Bool) :
    encrypt (a, b) (pureState (ket z)) = pureState (ket (z + a)) := by
  ext y y'
  simp only [encrypt, pauliString_mul_mul_conjTranspose_apply, pureState_apply, ket_apply]
  have hz (w : ι → Bool) : (w + a = z) ↔ (w = z + a) := by
    constructor <;> rintro rfl <;> simp
  simp only [hz]
  by_cases hy : y = z + a
  · by_cases hy' : y' = z + a
    · subst hy hy'
      simp only [ite_true, Cslib.BitString.add_cancel_right, star_one, mul_one]
      rw [← Complex.ofReal_mul, Cslib.BitString.signVal_mul_self, Complex.ofReal_one]
    · simp [hy, hy']
  · simp [hy]

-- A single ciphertext is not secret: with a fixed key the ciphertext of `|z⟩` is a basis state,
-- not the maximally mixed state, so averaging over the key is essential.
example (k : (Unit → Bool) × (Unit → Bool)) (z : Unit → Bool) :
    encrypt k (pureState (ket z)) ≠ (2 : ℂ)⁻¹ • (1 : Op Unit) := by
  intro h
  rw [encrypt_pureState_ket] at h
  have h1 := congrFun (congrFun h (z + k.1)) (z + k.1)
  simp [pureState_apply, ket_apply] at h1

-- One qubit: the average ciphertext of `|0⟩⟨0|` and of `|+⟩⟨+|` is `1 / 2`, and every pure qubit
-- state has the same average ciphertext, so without the key they are indistinguishable.
example : averageCiphertext (pureState (ket (fun _ : Unit => false))) =
    (2 : ℂ)⁻¹ • (1 : Op Unit) := by
  rw [averageCiphertext_eq (isDensityMatrix_pureState (norm_ket _))]
  norm_num

/-- `|+⟩` on the one-qubit register `Unit → Bool`. -/
noncomputable def plusOne : EuclideanSpace ℂ (Unit → Bool) :=
  WithLp.toLp 2 fun _ => (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)

theorem norm_plusOne : ‖plusOne‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp only [plusOne, Complex.norm_real, Real.norm_eq_abs, sq_abs, sum_const, card_univ,
    Fintype.card_fun, Fintype.card_unit, Fintype.card_bool, inv_pow,
    Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  norm_num

example : averageCiphertext (pureState plusOne) = (2 : ℂ)⁻¹ • (1 : Op Unit) := by
  rw [averageCiphertext_eq (isDensityMatrix_pureState norm_plusOne)]
  norm_num

example {ψ : EuclideanSpace ℂ (Unit → Bool)} (hψ : ‖ψ‖ = 1) :
    averageCiphertext (pureState ψ) = averageCiphertext (pureState (ket (fun _ : Unit => false))) :=
  averageCiphertext_eq_averageCiphertext (isDensityMatrix_pureState hψ)
    (isDensityMatrix_pureState (norm_ket _))

-- Without the trace-one hypothesis the twirl is `tr ρ / 2ⁿ • 1`: a traceless matrix twirls to zero.
example : averageCiphertext (pureState (ket (fun _ : Unit => false)) -
    pureState (ket (fun _ : Unit => true))) = 0 := by
  rw [averageCiphertext_eq_trace_smul, trace_sub, trace_pureState, trace_pureState, norm_ket,
    norm_ket, sub_self, zero_div, zero_smul]

-- Secrecy with a reference system: if Alice encrypts her half of an EPR pair, Eve's joint state
-- with Bob's half is `1 / 2 ⊗ 1 / 2`, the same as for two independent maximally mixed qubits.
example : averageCiphertextWith (pureState (maxEntangled (Unit → Bool))) =
    ((2 : ℂ)⁻¹ • (1 : Op Unit)) ⊗ₖ ((2 : ℂ)⁻¹ • (1 : Op Unit)) := by
  rw [averageCiphertextWith_eq, partialTraceLeft_pureState_maxEntangled]
  norm_num

private theorem partialTraceRight_ket_pair (i : Bool) (k : Fin 3) :
    partialTraceRight (pureState (ket (i, k))) = pureState (ket i) := by
  ext a b
  cases i <;> cases a <;> cases b <;>
    simp [partialTraceRight_apply, pureState_apply, ket_apply, Finset.sum_ite_eq']

-- Unequal local dimensions and rank-one reductions are allowed in the overlap theorem.
example :
    rootFidelity (partialTraceRight (pureState (ket (false, (0 : Fin 3)))))
      (partialTraceRight (pureState (ket (false, (1 : Fin 3))))) = 1 := by
  let ψ := ket (false, (0 : Fin 3))
  let φ := ket (false, (1 : Fin 3))
  have he : partialTraceRight (pureState ψ) = partialTraceRight (pureState φ) :=
    (partialTraceRight_ket_pair false 0).trans (partialTraceRight_ket_pair false 1).symm
  obtain ⟨U, hU, h⟩ := exists_localUnitary_of_partialTraceRight_eq ψ φ he
  change rootFidelity (partialTraceRight (pureState ψ)) (partialTraceRight (pureState φ)) = 1
  have hlo := inner_localUnitary_re_le_rootFidelity ψ φ U hU
  rw [h] at hlo
  have hφ : ‖φ‖ = 1 := norm_ket _
  have hself : (inner ℂ φ φ).re = 1 := by
    change RCLike.re (inner ℂ φ φ) = 1
    rw [inner_self_eq_norm_sq, hφ, one_pow]
  rw [hself] at hlo
  obtain ⟨_, _, hdist⟩ := exists_localUnitary_norm_sub_sq_eq ψ φ (norm_ket _) hφ
  have hhi := hdist ▸ sq_nonneg _
  linarith

private theorem traceNorm_orthogonal_qubit_states :
    (pureState (ket false) - pureState (ket true)).traceNorm = 2 := by
  let D : Matrix Bool Bool ℂ := diagonal fun b => if b then -1 else 1
  have hD : pureState (ket false) - pureState (ket true) = D := by
    ext i j
    cases i <;> cases j <;> simp [D, pureState_apply, ket_apply, diagonal]
  have hgram : Dᴴ * D = 1 := by
    unfold D
    rw [diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext b
    cases b <;> simp
  rw [hD, traceNorm, hgram, CFC.sqrt_one, trace_one]
  norm_num [Fintype.card_bool]

-- Orthogonal rank-one reductions have trace norm difference two, even with a larger purifier.
example :
    ∃ U ∈ unitaryGroup (Fin 3) ℂ,
      ‖WithLp.toLp 2 (((1 : Matrix Bool Bool ℂ) ⊗ₖ U) *ᵥ
        (ket (false, (0 : Fin 3))).ofLp) - ket (true, (1 : Fin 3))‖ ^ 2 ≤ 2 := by
  obtain ⟨U, hU, h⟩ := exists_localUnitary_norm_sub_sq_le_traceNorm
    (ket (false, (0 : Fin 3))) (ket (true, (1 : Fin 3))) (norm_ket _) (norm_ket _)
  refine ⟨U, hU, h.trans_eq ?_⟩
  rw [partialTraceRight_ket_pair, partialTraceRight_ket_pair]
  exact traceNorm_orthogonal_qubit_states
-- The upper inequality detects zero fidelity from maximal trace distance, including at
-- these singular density matrices.
example : rootFidelity (pureState (ket false)) (pureState (ket true)) = 0 := by
  have h := traceDistance_le_sqrt_one_sub_rootFidelity_sq
    (isDensityMatrix_pureState (norm_ket false)) (isDensityMatrix_pureState (norm_ket true))
  rw [traceDistance, traceNorm_orthogonal_qubit_states] at h
  have hOne : (1 : ℝ) ≤ Real.sqrt (1 - rootFidelity (pureState (ket false))
      (pureState (ket true)) ^ 2) := by simpa only [show (2 : ℝ) / 2 = 1 by norm_num] using h
  have hSq := (Real.le_sqrt' (by norm_num : (0 : ℝ) < 1)).mp hOne
  apply sq_eq_zero_iff.mp
  exact le_antisymm (by linarith) (sq_nonneg _)

-- Disjoint one-dimensional supports give infinite relative entropy.
private theorem relativeEntropy_orthogonal_qubit_states :
    relativeEntropy (pureState (ket false)) (pureState (ket true)) = ⊤ := by
  apply relativeEntropy_of_not_supportLE
  intro h
  let v := (ket false).ofLp
  have hz : (pureState (ket true)) *ᵥ v = 0 := by
    funext i
    cases i <;> simp [v, mulVec, dotProduct, pureState_apply, ket_apply]
  have he := congrFun (h v hz) false
  simp [v, mulVec, dotProduct, pureState_apply, ket_apply] at he

-- Zero relative entropy of the common rank-one reduction gives exact alignment even
-- when the original purifying vectors use different coordinates.
example : ∃ U ∈ unitaryGroup (Fin 3) ℂ,
    WithLp.toLp 2 (((1 : Matrix Bool Bool ℂ) ⊗ₖ U) *ᵥ
      (ket (false, (0 : Fin 3))).ofLp) = ket (false, (1 : Fin 3)) := by
  obtain ⟨U, hU, h⟩ := exists_localUnitary_norm_sub_sq_le_relativeEntropy
    (ket (false, (0 : Fin 3))) (ket (false, (1 : Fin 3))) (norm_ket _) (norm_ket _)
  rw [partialTraceRight_ket_pair, partialTraceRight_ket_pair, relativeEntropy_self,
    ← WithTop.coe_zero, WithTop.coe_le_coe] at h
  have hz := sq_eq_zero_iff.mp (le_antisymm h (sq_nonneg _))
  exact ⟨U, hU, sub_eq_zero.mp (norm_eq_zero.mp hz)⟩

-- An incompatible conditional block contributes zero when its source label has zero mass.
example : relativeEntropy
    (classicalQuantumState (PMF.pure false) (fun _ => pureState (ket false)))
    (classicalQuantumState (PMF.pure false) (fun x => pureState (ket x))) = 0 := by
  let : MeasurableSpace Bool := ⊤
  let : MeasurableSingletonClass Bool := ⟨fun _ => trivial⟩
  rw [relativeEntropy_classicalQuantumState _ _
    (fun _ => isDensityMatrix_pureState (norm_ket false))
    (fun x => isDensityMatrix_pureState (norm_ket x)), InformationTheory.klDiv_self,
    Fintype.sum_bool]
  simp [PMF.pure_apply]

-- At positive source mass, the same support failure gives infinite divergence.
example : relativeEntropy
    (classicalQuantumState (PMF.pure false) (fun _ => pureState (ket false)))
    (classicalQuantumState (PMF.pure false) (fun _ => pureState (ket true))) = ⊤ := by
  let : MeasurableSpace Bool := ⊤
  let : MeasurableSingletonClass Bool := ⟨fun _ => trivial⟩
  rw [relativeEntropy_classicalQuantumState _ _
    (fun _ => isDensityMatrix_pureState (norm_ket false))
    (fun _ => isDensityMatrix_pureState (norm_ket true)), InformationTheory.klDiv_self,
    Fintype.sum_bool]
  simp [PMF.pure_apply, relativeEntropy_orthogonal_qubit_states]

-- A deterministic classical label carries no information about its quantum block.
example : mutualInformation
    (classicalQuantumState (PMF.pure false) (fun x => pureState (ket x))) = 0 := by
  rw [mutualInformation_classicalQuantumState _ (fun x => isDensityMatrix_pureState (norm_ket x)),
    partialTraceRight_classicalQuantumState, Fintype.sum_bool, Fintype.sum_bool]
  simp [PMF.pure_apply]

-- A common reference orthogonal to the only active conditional state puts the
-- infinity in the marginal-divergence term of the decomposition.
example : relativeEntropy
    (partialTraceRight (classicalQuantumState (PMF.pure false) (fun x => pureState (ket x))))
    (pureState (ket true)) = ⊤ := by
  have h := sum_weighted_relativeEntropy_eq_mutualInformation_add (PMF.pure false)
    (fun x => isDensityMatrix_pureState (norm_ket x)) (pureState (ket true))
  rw [mutualInformation_classicalQuantumState_pure false
    (fun x => isDensityMatrix_pureState (norm_ket x)), zero_add, Fintype.sum_bool] at h
  simpa [PMF.pure_apply, relativeEntropy_orthogonal_qubit_states] using h.symm

-- Only the second label varies, and its two conditional qubit states are orthogonal.
-- The first label's null branch makes no contribution to the information chain.
example (q : PMF Bool) :
    let p := q.map (false, ·)
    mutualInformation (classicalQuantumState p (fun z => pureState (ket z.2))) =
      mutualInformation (classicalQuantumState (Cslib.Probability.PMF.conditionalSnd p false)
        (fun y => pureState (ket y))) := by
  dsimp only
  let p := q.map (false, ·)
  let ρ (z : Bool × Bool) := pureState (ket z.2)
  have hρ (z : Bool × Bool) : IsDensityMatrix (ρ z) := isDensityMatrix_pureState (norm_ket _)
  change mutualInformation (classicalQuantumState p ρ) = _
  have hp : p.map Prod.fst = PMF.pure false := by
    change (q.map (false, ·)).map Prod.fst = _
    rw [PMF.map_comp]
    exact PMF.map_const _ _
  have hzero : mutualInformation (classicalQuantumState (p.map Prod.fst)
      (quantumMarginalGiven p ρ)) = 0 := by
    rw [hp]
    exact mutualInformation_classicalQuantumState_pure false
      (isDensityMatrix_quantumMarginalGiven p hρ)
  rw [mutualInformation_classicalQuantumState_prod p hρ, hzero, zero_add, hp, Fintype.sum_bool]
  simp [PMF.pure_apply, p, ρ]

-- An empty classical register has zero information under any label law.
example (p : PMF (Fin 0 → Bool)) :
    mutualInformation (classicalQuantumState p (fun _ => pureState (ket false))) = 0 := by
  rw [mutualInformation_classicalQuantumState_eq_sum_coordinates (fun _ : Fin 0 => Bool) p
    (fun _ => isDensityMatrix_pureState (norm_ket false))]
  simp

private abbrev twoLabelAlphabet (i : Fin 2) : Type :=
  Fin.cases (motive := fun _ => Type) Bool (fun _ => Fin 3) i

local instance (i : Fin 2) : Fintype (twoLabelAlphabet i) :=
  Fin.cases (motive := fun j => Fintype (twoLabelAlphabet j))
    (inferInstanceAs (Fintype Bool)) (fun _ => inferInstanceAs (Fintype (Fin 3))) i

local instance (i : Fin 2) : DecidableEq (twoLabelAlphabet i) :=
  Fin.cases (motive := fun j => DecidableEq (twoLabelAlphabet j))
    (inferInstanceAs (DecidableEq Bool)) (fun _ => inferInstanceAs (DecidableEq (Fin 3))) i

-- The chain accepts a Boolean label followed by a ternary label.
example (p : PMF (∀ i, twoLabelAlphabet i)) :
    let ρ (z : ∀ i, twoLabelAlphabet i) := pureState (ket (z 0 : Bool))
    mutualInformation (classicalQuantumState p ρ) =
      ((coordinateMutualInformationTerms twoLabelAlphabet p ρ 0 +
        coordinateMutualInformationTerms twoLabelAlphabet p ρ 1 : ℝ) : WithTop ℝ) := by
  dsimp only
  rw [mutualInformation_classicalQuantumState_eq_sum_coordinates twoLabelAlphabet p
    (fun z => isDensityMatrix_pureState (norm_ket (z 0 : Bool))), Fin.sum_univ_two]

end CslibFrontierTests.QuantumDensity
