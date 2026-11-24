/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Circuit.Quantum.SuperdenseCoding
public import CslibFrontier.Computability.Circuit.Quantum.Teleportation
public import CslibFrontier.Foundations.Quantum.DensityMatrix.NoCloning
public import CslibFrontier.Foundations.Quantum.NoCloning
public import CslibFrontierTests.QuantumState

/-! Teleportation (including entangled teleportation and entanglement swapping), superdense coding,
pure-state no-cloning (ancilla-free and apparatus-assisted), and mixed-state Kraus no-cloning:
concrete instances and boundary witnesses. -/

public section

namespace CslibFrontierTests.QuantumProtocols

open Cslib.Quantum Matrix Gate
open scoped Kronecker InnerProductSpace TensorProduct ComplexOrder

/-! ### Teleportation -/

-- Teleporting `|0⟩`: Alice's outcome is uniform and Bob ends with `|0⟩`.
example : (measure (teleportState (ket false))
      ((norm_teleportState _).trans (norm_ket false))).map Prod.fst =
    Cslib.Probability.PMF.uniformOfFintype (Bool × Bool) :=
  measure_teleportState_map_fst _ (norm_ket false)

example (a b : Bool) :
    unitaryEquiv (teleportCorrection a b) (postMeasure (a, b) (teleportState (ket false))) =
      ket false :=
  teleportCorrection_postMeasure _ (norm_ket false) a b

-- Teleporting `|1⟩`: for every outcome Bob's corrected qubit is `|1⟩`. Before Alice measures, the
-- amplitude of `|1, 1, 0⟩` is `-1/2`, since `X Z |1⟩ = -|0⟩`.
example (a b : Bool) :
    unitaryEquiv (teleportCorrection a b) (postMeasure (a, b) (teleportState (ket true))) =
      ket true :=
  teleportCorrection_postMeasure _ (norm_ket true) a b

example : (teleportState (ket true)).ofLp ((true, true), false) = -(1 / 2) := by
  rw [teleportState_apply]
  norm_num

-- Teleporting `|+⟩`: for every outcome Bob's corrected qubit is `|+⟩`.
example (a b : Bool) :
    unitaryEquiv (teleportCorrection a b) (postMeasure (a, b) (teleportState plus)) = plus :=
  teleportCorrection_postMeasure _ norm_plus a b

-- Before Alice measures, the amplitude of `|1, 1, 0⟩` in the teleportation of `|+⟩` is
-- `-1/(2√2)`.
example : (teleportState plus).ofLp ((true, true), false) =
    -(1 / 2 * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) := by
  rw [teleportState_apply, plus_apply]
  norm_num

/-! ### Entangled teleportation and entanglement swapping -/

-- Entanglement swapping (`Ψ = bell`): before Alice acts, Charlie and Bob have never interacted and
-- their reduced two-qubit state is maximally mixed `(1/4) • 1` (product `(I/2) ⊗ (I/2)`).
example : partialTraceLeft (pureState (teleportEntangledInput bell)) =
    (1 / 4 : ℂ) • (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) := by
  have hs : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = 1 / 2 := by
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]
    norm_num
  ext ⟨r₁, c₁⟩ ⟨r₂, c₂⟩
  simp only [partialTraceLeft_apply, pureState_apply, teleportEntangledInput_apply, bell_apply,
    Fintype.sum_prod_type, Matrix.smul_apply, Matrix.one_apply, Prod.mk.injEq, smul_eq_mul]
  cases r₁ <;> cases c₁ <;> cases r₂ <;> cases c₂ <;>
    simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, and_self, and_false, false_and,
      Fintype.sum_bool, mul_zero, zero_mul, add_zero, zero_add, mul_one, star_mul',
      Complex.star_def, map_zero, Complex.conj_ofReal, hs] <;>
    norm_num

-- Entanglement swapping: Alice's measurement outcome on `Bool × Bool` is uniform, and for every
-- outcome `(a, b)`, Bob's local correction leaves Charlie and Bob in the Bell state `bell`.
example : (measure (teleportEntangledState bell)
      ((norm_teleportEntangledState bell).trans norm_bell)).map Prod.fst =
    Cslib.Probability.PMF.uniformOfFintype (Bool × Bool) ∧
  ∀ a b : Bool,
    unitaryEquiv (onSecond (teleportCorrection a b))
      (postMeasure (a, b) (teleportEntangledState bell)) = bell :=
  teleportation_entangled bell norm_bell

-- Non-qubit reference register `Fin 3`: teleporting the qubit half of `|(0, true)⟩`.
example (a b : Bool) :
    unitaryEquiv (onSecond (teleportCorrection a b))
      (postMeasure (a, b) (teleportEntangledState (ket ((0 : Fin 3), true)))) =
    ket ((0 : Fin 3), true) :=
  teleportCorrection_postMeasure_entangled _ (norm_ket _) a b

/-! ### Superdense coding -/

-- Bob decodes each of the four messages exactly.
example : measure (superdenseState false false) (norm_superdenseState _ _) =
    PMF.pure (false, false) :=
  superdense_coding false false

example : measure (superdenseState false true) (norm_superdenseState _ _) =
    PMF.pure (false, true) :=
  superdense_coding false true

example : measure (superdenseState true false) (norm_superdenseState _ _) =
    PMF.pure (true, false) :=
  superdense_coding true false

example : measure (superdenseState true true) (norm_superdenseState _ _) =
    PMF.pure (true, true) :=
  superdense_coding true true

-- For the message `(1, 1)` Bob's state carries the global phase `-1`, which the measurement
-- does not see.
example : superdenseState true true = (-1 : ℂ) • ket (true, true) := by
  rw [superdenseState_eq]
  norm_num

/-! ### No-cloning (ancilla-free) -/

-- The CNOT clones both computational basis states, which are orthogonal: the dichotomy of
-- `inner_eq_zero_or_eq_of_unitary_clone` allows this.
example (b : Bool) :
    cnotMatrix *ᵥ (prodState (ket b) (ket false)).ofLp = (prodState (ket b) (ket b)).ofLp := by
  ext ⟨x, y⟩
  cases b <;> cases x <;> cases y <;> simp

theorem inner_ket_false_plus : ⟪ket false, plus⟫_ℂ = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) := by
  rw [ket, EuclideanSpace.inner_single_left, plus_apply]
  simp

-- The CNOT does not clone `|+⟩`: `|0⟩` and `|+⟩` are neither orthogonal nor equal.
example : cnotMatrix *ᵥ (prodState plus (ket false)).ofLp ≠ (prodState plus plus).ofLp := by
  intro h
  have h0 : cnotMatrix *ᵥ (prodState (ket false) (ket false)).ofLp =
      (prodState (ket false) (ket false)).ofLp := by
    ext ⟨x, y⟩
    cases x <;> cases y <;> simp
  rcases inner_eq_zero_or_eq_of_unitary_clone cnotMatrix_mem_unitaryGroup (norm_ket false)
      norm_plus (norm_ket false) h0 h with h' | h'
  · rw [inner_ket_false_plus] at h'
    simp at h'
  · have h1 := congrArg (fun v : EuclideanSpace ℂ Bool => v.ofLp true) h'
    simp only [ket_apply, plus_apply, Bool.true_eq_false, ↓reduceIte] at h1
    exact Complex.ofReal_ne_zero.mpr (by positivity) h1.symm

-- No matrix on two qubits clones every unit qubit.
example : ¬ ∃ U : Matrix (Bool × Bool) (Bool × Bool) ℂ, ∀ ψ : EuclideanSpace ℂ Bool, ‖ψ‖ = 1 →
    U *ᵥ (prodState ψ (ket false)).ofLp = (prodState ψ ψ).ofLp :=
  not_exists_matrix_clone (ket false)

-- Not even up to a nonzero state-dependent factor.
example : ¬ ∃ (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) (c : EuclideanSpace ℂ Bool → ℂ),
    ∀ ψ : EuclideanSpace ℂ Bool, ‖ψ‖ = 1 →
      c ψ ≠ 0 ∧ U *ᵥ (prodState ψ (ket false)).ofLp = c ψ • (prodState ψ ψ).ofLp :=
  not_exists_matrix_clone_smul (ket false)

-- The hypothesis `Nontrivial ι` of `not_exists_matrix_clone_smul` is needed: in dimension 1 the
-- identity clones every unit state up to the nonzero factor `1/ψ`.
example : ∃ (U : Matrix (Unit × Unit) (Unit × Unit) ℂ) (c : EuclideanSpace ℂ Unit → ℂ),
    ∀ ψ : EuclideanSpace ℂ Unit, ‖ψ‖ = 1 →
      c ψ ≠ 0 ∧ U *ᵥ (prodState ψ (ket ())).ofLp = c ψ • (prodState ψ ψ).ofLp := by
  refine ⟨1, fun ψ => (ψ.ofLp ())⁻¹, fun ψ hψ => ?_⟩
  have h0 : ψ.ofLp () ≠ 0 := by
    intro h
    have : ψ = 0 := by ext u; cases u; simpa using h
    simp [this] at hψ
  refine ⟨inv_ne_zero h0, ?_⟩
  ext ⟨⟨⟩, ⟨⟩⟩
  simp only [one_mulVec, prodState_apply, ket_apply, ite_true, mul_one, Pi.smul_apply,
    smul_eq_mul]
  field_simp

-- No linear map on `ℂ² ⊗ ℂ²` clones every unit vector of `ℂ²`.
example : ¬ ∃ L : EuclideanSpace ℂ (Fin 2) ⊗[ℂ] EuclideanSpace ℂ (Fin 2) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin 2) ⊗[ℂ] EuclideanSpace ℂ (Fin 2),
    ∀ ψ : EuclideanSpace ℂ (Fin 2), ‖ψ‖ = 1 → L (ψ ⊗ₜ EuclideanSpace.single 0 1) = ψ ⊗ₜ ψ := by
  refine not_exists_linearMap_clone ?_ _
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace, Fintype.card_fin]
  norm_num

/-! ### Apparatus-assisted (Wootters–Zurek) no-cloning: subtle boundary witnesses -/

-- Subtle boundary 1: WITHOUT an apparatus, no unitary on `Bool × Bool` clones both `|0⟩` and
-- `-|0⟩` onto `|0⟩` (`(-|0⟩) ⊗ (-|0⟩) = |00⟩ ≠ -|00⟩`).
example : ¬ ∃ U : Matrix (Bool × Bool) (Bool × Bool) ℂ, U ∈ unitaryGroup (Bool × Bool) ℂ ∧
    U *ᵥ (prodState (ket false) (ket false)).ofLp = (prodState (ket false) (ket false)).ofLp ∧
    U *ᵥ (prodState (-ket false) (ket false)).ofLp =
      (prodState (-ket false) (-ket false)).ofLp := by
  rintro ⟨U, hU, h0, hm0⟩
  have hm_norm : ‖-ket false‖ = 1 := by rw [norm_neg, norm_ket]
  rcases inner_eq_zero_or_eq_of_unitary_clone hU (norm_ket false) hm_norm (norm_ket false) h0 hm0
      with hinn | heq
  · rw [inner_neg_right, inner_self_eq_one_of_norm_eq_one (norm_ket false)] at hinn
    norm_num at hinn
  · have hf := congrArg (fun v : EuclideanSpace ℂ Bool => v.ofLp false) heq
    simp only [WithLp.ofLp_neg, Pi.neg_apply, ket_apply, ↓reduceIte] at hf
    norm_num at hf

-- WITH an apparatus (`(Bool × Bool) × Bool`), `onFirst cnotMatrix` DOES clone both `|0⟩` (with
-- final apparatus `|0⟩`) and `-|0⟩` (with final apparatus `-|0⟩`), inhabiting the collinear
-- `φ = c • ψ` (`c = -1`) branch of `inner_eq_zero_or_exists_smul_of_unitary_clone_apparatus`.
example :
    let U : Matrix ((Bool × Bool) × Bool) ((Bool × Bool) × Bool) ℂ :=
      onFirst (κ := Bool) ⟨cnotMatrix, cnotMatrix_mem_unitaryGroup⟩
    U ∈ unitaryGroup ((Bool × Bool) × Bool) ℂ ∧
      U *ᵥ (prodState (prodState (ket false) (ket false)) (ket false)).ofLp =
        (prodState (prodState (ket false) (ket false)) (ket false)).ofLp ∧
      U *ᵥ (prodState (prodState (-ket false) (ket false)) (ket false)).ofLp =
        (prodState (prodState (-ket false) (-ket false)) (-ket false)).ofLp := by
  refine ⟨(onFirst ⟨cnotMatrix, cnotMatrix_mem_unitaryGroup⟩).property, ?_, ?_⟩
  · ext ⟨⟨x, y⟩, z⟩
    rw [coe_onFirst, kronecker_one_mulVec_apply]
    cases x <;> cases y <;> cases z <;> simp
  · ext ⟨⟨x, y⟩, z⟩
    rw [coe_onFirst, kronecker_one_mulVec_apply]
    cases x <;> cases y <;> cases z <;> simp

-- Subtle boundary 2: even with an arbitrary finite apparatus `α`, no unitary clones both `|0⟩`
-- and `|+⟩`, since they are neither orthogonal nor collinear.
example {α : Type*} [Fintype α] [DecidableEq α] (a₀ aψ aφ : EuclideanSpace ℂ α)
    (ha₀ : ‖a₀‖ = 1) :
    ¬ ∃ U : Matrix ((Bool × Bool) × α) ((Bool × Bool) × α) ℂ,
      U ∈ unitaryGroup ((Bool × Bool) × α) ℂ ∧
      U *ᵥ (prodState (prodState (ket false) (ket false)) a₀).ofLp =
        (prodState (prodState (ket false) (ket false)) aψ).ofLp ∧
      U *ᵥ (prodState (prodState plus (ket false)) a₀).ofLp =
        (prodState (prodState plus plus) aφ).ofLp := by
  rintro ⟨U, hU, h0, hp⟩
  rcases inner_eq_zero_or_exists_smul_of_unitary_clone_apparatus hU (norm_ket false) norm_plus
      (norm_ket false) ha₀ h0 hp with hinn | ⟨c, _, hcol⟩
  · rw [inner_ket_false_plus] at hinn
    simp at hinn
  · have ht := congrArg (fun v : EuclideanSpace ℂ Bool => v.ofLp true) hcol
    simp only [WithLp.ofLp_smul, Pi.smul_apply, plus_apply, ket_apply, Bool.true_eq_false,
      ↓reduceIte, smul_eq_mul, mul_zero] at ht
    exact Complex.ofReal_ne_zero.mpr (by positivity) ht

-- Subtle boundary 3: `Nontrivial ι` is sharp even for unitary apparatus-assisted cloning! On
-- `Unit`, the identity unitary `1` clones EVERY unit state `ψ` with unit post-apparatus
-- `star (ψ ()) • ket ()`.
example : ∃ U : Matrix ((Unit × Unit) × Unit) ((Unit × Unit) × Unit) ℂ,
    U ∈ unitaryGroup ((Unit × Unit) × Unit) ℂ ∧
    ∀ ψ : EuclideanSpace ℂ Unit, ‖ψ‖ = 1 →
      ∃ aψ : EuclideanSpace ℂ Unit, ‖aψ‖ = 1 ∧
        U *ᵥ (prodState (prodState ψ (ket ())) (ket ())).ofLp =
          (prodState (prodState ψ ψ) aψ).ofLp := by
  refine ⟨1, one_mem _, fun ψ hψ => ?_⟩
  have hn : ‖ψ.ofLp ()‖ = 1 := by
    have hsq : ‖ψ.ofLp ()‖ ^ 2 = 1 ^ 2 := by
      rw [← Fintype.sum_unique fun u : Unit => ‖ψ.ofLp u‖ ^ 2, ← EuclideanSpace.norm_sq_eq, hψ]
    exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp hsq
  refine ⟨star (ψ.ofLp ()) • ket (), by rw [norm_smul, norm_star, hn, norm_ket, one_mul], ?_⟩
  have hmul : ψ.ofLp () * star (ψ.ofLp ()) = 1 := by
    rw [mul_comm, Complex.star_def, RCLike.conj_mul, hn]
    norm_num
  ext ⟨⟨⟨⟩, ⟨⟩⟩, ⟨⟩⟩
  simp only [one_mulVec, prodState_apply, ket_apply, ↓reduceIte, WithLp.ofLp_smul,
    Pi.smul_apply, smul_eq_mul, mul_one, mul_assoc, hmul]

-- Universal impossibility with apparatus on qubits and on `(ℂ² ⊗ ℂ²) ⊗ ℂ²`.
example : ¬ ∃ U : Matrix ((Bool × Bool) × Bool) ((Bool × Bool) × Bool) ℂ,
    ∀ ψ : EuclideanSpace ℂ Bool, ‖ψ‖ = 1 →
      ∃ aψ : EuclideanSpace ℂ Bool, aψ ≠ 0 ∧
        U *ᵥ (prodState (prodState ψ (ket false)) (ket false)).ofLp =
          (prodState (prodState ψ ψ) aψ).ofLp :=
  not_exists_matrix_clone_apparatus (ket false) (ket false)

example : ¬ ∃ L : (EuclideanSpace ℂ (Fin 2) ⊗[ℂ] EuclideanSpace ℂ (Fin 2)) ⊗[ℂ]
        EuclideanSpace ℂ (Fin 2) →ₗ[ℂ]
      (EuclideanSpace ℂ (Fin 2) ⊗[ℂ] EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] EuclideanSpace ℂ (Fin 2),
    ∀ ψ : EuclideanSpace ℂ (Fin 2), ‖ψ‖ = 1 →
      ∃ aψ : EuclideanSpace ℂ (Fin 2), aψ ≠ 0 ∧
        L ((ψ ⊗ₜ EuclideanSpace.single 0 1) ⊗ₜ EuclideanSpace.single 0 1) =
          (ψ ⊗ₜ ψ) ⊗ₜ aψ := by
  refine not_exists_linearMap_clone_apparatus ?_ _ _
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace, Fintype.card_fin]
  norm_num

/-! ### Mixed-state CPTP Kraus no-cloning -/

/-- Rank-2 mixed state `|b⟩⟨b| ⊗ (I/2)` on two qubits `Bool × Bool`. -/
noncomputable def mixedBlock (b : Bool) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  pureState (ket b) ⊗ₖ ((1 / 2 : ℂ) • (1 : Matrix Bool Bool ℂ))

theorem isDensityMatrix_mixedBlock (b : Bool) : IsDensityMatrix (mixedBlock b) := by
  refine ⟨?_, ?_⟩
  · let R := pureState (ket b) ⊗ₖ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (1 : Matrix Bool Bool ℂ))
    have hfac : Rᴴ * R = mixedBlock b := by
      have hs : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = 1 / 2 := by
        rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]
        norm_num
      ext ⟨x₁, y₁⟩ ⟨x₂, y₂⟩
      rw [Matrix.mul_apply, Fintype.sum_prod_type]
      simp only [R, mixedBlock, conjTranspose_apply, kroneckerMap_apply, pureState_apply,
        ket_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, star_mul',
        Complex.star_def, Complex.conj_ofReal]
      cases b <;> cases x₁ <;> cases y₁ <;> cases x₂ <;> cases y₂ <;>
        simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, Fintype.sum_bool,
          mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul, map_one, map_zero, hs]
    exact hfac ▸ posSemidef_conjTranspose_mul_self R
  · simp [mixedBlock, trace_kronecker, trace_pureState]

-- `mixedBlock false` is genuinely mixed (`ρ² ≠ ρ`), distinct from `mixedBlock true`, and
-- orthogonal to `mixedBlock true` (`ρ₀ * ρ₁ = 0`).
example : mixedBlock false * mixedBlock false ≠ mixedBlock false ∧
    mixedBlock false ≠ mixedBlock true ∧
    mixedBlock false * mixedBlock true = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro hpure
    have h00 := congrFun (congrFun hpure (false, false)) (false, false)
    rw [Matrix.mul_apply, Fintype.sum_prod_type] at h00
    simp only [mixedBlock, kroneckerMap_apply, pureState_apply, ket_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul, Fintype.sum_bool] at h00
    norm_num at h00
  · intro heq
    have h00 := congrFun (congrFun heq (false, false)) (false, false)
    simp only [mixedBlock, kroneckerMap_apply, pureState_apply, ket_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul] at h00
    norm_num at h00
  · ext ⟨x₁, y₁⟩ ⟨x₂, y₂⟩
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    simp only [mixedBlock, kroneckerMap_apply, pureState_apply, ket_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul, Matrix.zero_apply, Fintype.sum_bool]
    cases x₁ <;> cases y₁ <;> cases x₂ <;> cases y₂ <;> norm_num

/-- A 16-operator CPTP Kraus channel on `Bool × Bool` that clones both genuinely mixed states
`mixedBlock false` and `mixedBlock true` (`ρ₀ * ρ₁ = 0`). -/
noncomputable def mixedBlockCloner :
    Bool × Bool × Bool × Bool →
      Matrix ((Bool × Bool) × (Bool × Bool)) (Bool × Bool) ℂ :=
  fun ⟨b, x, y₁, y₂⟩ => (1 / 2 : ℂ) • Matrix.single ((b, y₁), (b, y₂)) (b, x) 1

example :
    (∑ j : Bool × Bool × Bool × Bool, (mixedBlockCloner j)ᴴ * mixedBlockCloner j = 1) ∧
    ∀ b : Bool,
      ∑ j : Bool × Bool × Bool × Bool,
        mixedBlockCloner j * mixedBlock b * (mixedBlockCloner j)ᴴ =
          mixedBlock b ⊗ₖ mixedBlock b := by
  refine ⟨?_, fun b => ?_⟩
  · ext ⟨b₁, x₁⟩ ⟨b₂, x₂⟩
    simp only [mixedBlockCloner, conjTranspose_smul, conjTranspose_single, star_one,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, single_mul_single_same, mul_one,
      Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, Matrix.one_apply, Prod.mk.injEq,
      smul_eq_mul, Fintype.sum_prod_type, Fintype.sum_bool]
    cases b₁ <;> cases x₁ <;> cases b₂ <;> cases x₂ <;> norm_num
  · have hsingle (p : (Bool × Bool) × (Bool × Bool)) (q : Bool × Bool)
        (M : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
        Matrix.single p q (1 : ℂ) * M * (Matrix.single p q (1 : ℂ))ᴴ =
          M q q • Matrix.single p p 1 := by
      ext r s
      rw [Matrix.mul_apply]
      simp only [conjTranspose_single, star_one, Matrix.mul_apply, Matrix.single_apply,
        Matrix.smul_apply, smul_eq_mul]
      by_cases hr : p = r
      · by_cases hrs : r = s
        · simp [hr, hrs]
        · simp [hr, hrs]
      · simp [hr]
    have hterm (b' x y₁ y₂ : Bool) :
        mixedBlockCloner (b', x, y₁, y₂) * mixedBlock b *
          (mixedBlockCloner (b', x, y₁, y₂))ᴴ =
          ((1 / 4 : ℂ) * mixedBlock b (b', x) (b', x)) •
            Matrix.single ((b', y₁), (b', y₂)) ((b', y₁), (b', y₂)) 1 := by
      simp only [mixedBlockCloner, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
        hsingle, smul_smul]
      congr 1
      norm_num
      ring
    ext ⟨⟨u₁, v₁⟩, ⟨u₂, v₂⟩⟩ ⟨⟨w₁, z₁⟩, ⟨w₂, z₂⟩⟩
    simp only [Fintype.sum_prod_type, hterm, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.single_apply, Prod.mk.injEq, smul_eq_mul]
    by_cases h : u₁ = u₂ ∧ u₁ = w₁ ∧ v₁ = z₁ ∧ w₁ = w₂ ∧ v₂ = z₂
    · rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩
      cases b <;> cases u₁ <;> cases v₁ <;> cases v₂ <;>
        simp [mixedBlock] <;> norm_num
    · have hzero (b' x y₁ y₂ : Bool) :
          (1 / 4 : ℂ) * mixedBlock b (b', x) (b', x) *
            (if ((b' = u₁ ∧ y₁ = v₁) ∧ b' = u₂ ∧ y₂ = v₂) ∧
                (b' = w₁ ∧ y₁ = z₁) ∧ b' = w₂ ∧ y₂ = z₂ then 1 else 0) = 0 := by
        split_ifs with hc
        · rcases hc with ⟨⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩, ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩⟩
          exact False.elim (h ⟨rfl, rfl, rfl, rfl, rfl⟩)
        · simp
      trans (0 : ℂ)
      · exact Finset.sum_eq_zero fun b' _ => Finset.sum_eq_zero fun x _ =>
          Finset.sum_eq_zero fun y₁ _ => Finset.sum_eq_zero fun y₂ _ => hzero b' x y₁ y₂
      · symm
        change (pureState (ket b) u₁ w₁ * (((1 / 2 : ℂ) • (1 : Matrix Bool Bool ℂ)) v₁ z₁)) *
            (pureState (ket b) u₂ w₂ * (((1 / 2 : ℂ) • (1 : Matrix Bool Bool ℂ)) v₂ z₂)) = 0
        simp only [pureState_apply, ket_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
        by_cases hu₁ : u₁ = b; swap; · simp [hu₁]
        by_cases hw₁ : w₁ = b; swap; · simp [hw₁]
        by_cases hv₁ : v₁ = z₁; swap; · simp [hv₁]
        by_cases hu₂ : u₂ = b; swap; · simp [hu₂]
        by_cases hw₂ : w₂ = b; swap; · simp [hw₂]
        by_cases hv₂ : v₂ = z₂; swap; · simp [hv₂]
        exact False.elim (h ⟨hu₁.trans hu₂.symm, hu₁.trans hw₁.symm, hv₁, hw₁.trans hw₂.symm, hv₂⟩)

-- Negative mixed-state witness: no CPTP Kraus channel on a qubit clones every density matrix.
example {α : Type*} (s : Finset α) :
    ¬ ∃ K : α → Matrix (Bool × Bool) Bool ℂ, (∑ j ∈ s, (K j)ᴴ * K j = 1) ∧
      ∀ ρ : Matrix Bool Bool ℂ, IsDensityMatrix ρ → ∑ j ∈ s, K j * ρ * (K j)ᴴ = ρ ⊗ₖ ρ :=
  not_exists_kraus_clone s

/-! ### Pauli matrices and the Bell state -/

-- `X` and `Z` do not commute.
example : pauliZ * pauliX ≠ pauliX * pauliZ := by
  intro h
  have := congrFun (congrFun h false) true
  norm_num [Matrix.mul_apply] at this

-- `⟨Φ⁺| Z ⊗ Z |Φ⁺⟩ = 1`: the Bell state is a `+1` eigenvector of `Z ⊗ Z`.
example : star bell.ofLp ⬝ᵥ ((pauliZ ⊗ₖ pauliZ) *ᵥ bell.ofLp) = 1 := by
  rw [bell_eq_maxEntangled, star_maxEntangled_dotProduct_kronecker_mulVec_eq_trace]
  simp [Matrix.trace, Matrix.mul_apply]

end CslibFrontierTests.QuantumProtocols
