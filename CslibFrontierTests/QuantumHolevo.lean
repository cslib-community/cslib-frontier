/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Circuit.Quantum.SuperdenseCoding
public import CslibFrontier.Crypto.Protocols.Quantum.KeyLowerBound

/-! Holevo's bound, superdense-coding optimality, and the `2n`-bit private-quantum-channel key
lower bound: concrete tight instances and model-boundary witnesses. -/

public section

namespace CslibFrontierTests.QuantumHolevo

open Cslib.Quantum Cslib.Crypto.Protocols.Quantum Matrix Finset
open Cslib.Probability.PMF
open scoped ComplexOrder Kronecker

/-! ### Von Neumann entropy and Araki–Lieb on the Bell state -/

-- The joint EPR state is pure (`S(AB) = 0`), whereas both reduced qubits are maximally mixed
-- (`S(A) = S(B) = 1`), saturating Araki–Lieb `S(B) - S(A) ≤ S(AB)` at `0 ≤ 0`.
example : vonNeumannEntropy (pureState bell) = 0 :=
  vonNeumannEntropy_pureState norm_bell

example : vonNeumannEntropy (partialTraceRight (pureState bell)) = 1 := by
  rw [bell_eq_maxEntangled, partialTraceRight_pureState_maxEntangled,
    vonNeumannEntropy_maximallyMixed, Fintype.card_bool, Nat.cast_ofNat, Real.logb,
    div_self (Real.log_pos (by norm_num)).ne']

example : vonNeumannEntropy (partialTraceLeft (pureState bell)) = 1 := by
  rw [← vonNeumannEntropy_partialTrace_pureState_eq bell, bell_eq_maxEntangled,
    partialTraceRight_pureState_maxEntangled, vonNeumannEntropy_maximallyMixed,
    Fintype.card_bool, Nat.cast_ofNat, Real.logb, div_self (Real.log_pos (by norm_num)).ne']

/-! ### Mutual information of an exact channel -/

private theorem mutualInfo_bind_pure {X : Type*} [Finite X] (p : PMF X) :
    mutualInfo (p.bind fun x => (PMF.pure x).map (x, ·)) = entropy p := by
  simp_rw [PMF.pure_map]
  rw [← Function.comp_def, PMF.bind_pure_comp, mutualInfo_map,
    entropy_map_of_injective p (fun _ _ h => (Prod.mk.inj h).1),
    show (fun x : X => x) = id from rfl, PMF.map_id, add_sub_cancel_right]

/-! ### Tightness of Holevo's bound on one unassisted qubit -/

-- Sending a uniform computational-basis state `|b⟩` and measuring in the computational basis
-- achieves `I(X : Y) = χ = 1`, saturating `mutualInfo_measureDensity_le_holevoInformation` and
-- `mutualInfo_measureDensity_le_logb_card`.
example :
    holevoInformation (uniformOfFintype Bool) (fun b => pureState (ket b)) = 1 := by
  have havg :
      (∑ b : Bool, (uniformOfFintype Bool b).toReal • pureState (ket b)) =
        (Fintype.card Bool : ℂ)⁻¹ • (1 : Matrix Bool Bool ℂ) := by
    ext i j
    rw [Fintype.sum_bool]
    cases i <;> cases j <;>
      simp [uniformOfFintype_apply, pureState_apply, Fintype.card_bool]
  rw [holevoInformation, havg, vonNeumannEntropy_maximallyMixed]
  simp only [vonNeumannEntropy_pureState (norm_ket _), mul_zero, Finset.sum_const_zero, sub_zero,
    Fintype.card_bool, Nat.cast_ofNat]
  rw [Real.logb, div_self (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']

example :
    mutualInfo ((uniformOfFintype Bool).bind fun b =>
      (POVM.basis.measureDensity (pureState (ket b))
        (isDensityMatrix_pureState (norm_ket b))).map (b, ·)) = 1 := by
  have hmeas (b : Bool) :
      POVM.basis.measureDensity (pureState (ket b)) (isDensityMatrix_pureState (norm_ket b)) =
        PMF.pure b := by
    rw [POVM.measureDensity_pureState _ _ (norm_ket b), POVM.measure_basis]
    ext c
    by_cases h : c = b
    · subst h; simp
    · simp [h]
  simp_rw [hmeas]
  rw [mutualInfo_bind_pure, entropy_uniform, Fintype.card_bool, Nat.cast_ofNat,
    Real.logb, div_self (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']

/-! ### Superdense coding attains the `2`-bit entanglement-assisted Holevo cap -/

/-- Bob's superdense-coding measurement as a two-qubit POVM: pull back `POVM.basis` along
`superdenseDecoding`. -/
noncomputable def superdensePOVM : POVM (Bool × Bool) (Bool × Bool) :=
  POVM.basis.comap (superdenseDecoding : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    superdenseDecoding.property

theorem measureDensity_superdensePOVM (ab : Bool × Bool) :
    superdensePOVM.measureDensity
      (((superdenseEncoding ab.1 ab.2 : Matrix Bool Bool ℂ) ⊗ₖ (1 : Matrix Bool Bool ℂ)) *
        pureState bell *
        ((superdenseEncoding ab.1 ab.2 : Matrix Bool Bool ℂ) ⊗ₖ (1 : Matrix Bool Bool ℂ))ᴴ)
      ((isDensityMatrix_pureState norm_bell).conj_unitary
        (kronecker_mem_unitary (superdenseEncoding ab.1 ab.2).property (one_mem _))) =
      PMF.pure ab := by
  let enc : unitaryGroup (Bool × Bool) ℂ := onFirst (superdenseEncoding ab.1 ab.2)
  let ψ := unitaryEquiv enc bell
  have hpure :
      ((superdenseEncoding ab.1 ab.2 : Matrix Bool Bool ℂ) ⊗ₖ (1 : Matrix Bool Bool ℂ)) *
        pureState bell *
        ((superdenseEncoding ab.1 ab.2 : Matrix Bool Bool ℂ) ⊗ₖ (1 : Matrix Bool Bool ℂ))ᴴ =
      pureState ψ := by
    ext p q
    simp only [ψ, enc, unitaryEquiv_apply, coe_onFirst, pureState_apply, Matrix.mul_apply,
      conjTranspose_apply, mulVec, dotProduct, star_sum, star_mul']
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  ext out
  have hd :
      superdensePOVM.densityProb
        (((superdenseEncoding ab.1 ab.2 : Matrix Bool Bool ℂ) ⊗ₖ (1 : Matrix Bool Bool ℂ)) *
          pureState bell *
          ((superdenseEncoding ab.1 ab.2 : Matrix Bool Bool ℂ) ⊗ₖ (1 : Matrix Bool Bool ℂ))ᴴ) out =
        (PMF.pure ab out).toReal := by
    rw [hpure, POVM.densityProb_pureState, superdensePOVM, POVM.prob_comap]
    have hst : WithLp.toLp 2 ((superdenseDecoding : Matrix (Bool × Bool) (Bool × Bool) ℂ) *ᵥ
        ψ.ofLp) = superdenseState ab.1 ab.2 := by
      rw [← unitaryEquiv_apply, ← superdenseState_def]
    rw [hst, POVM.prob_basis]
    have hsc := congrArg (fun m : PMF (Bool × Bool) => m out) (superdense_coding ab.1 ab.2)
    rw [measure_apply] at hsc
    have hto := congrArg ENNReal.toReal hsc
    rwa [ENNReal.toReal_ofReal (by positivity)] at hto
  rw [POVM.measureDensity_apply, hd, ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]

-- Superdense coding achieves `2` bits of mutual information on one transmitted qubit (`Bool`),
-- matching the `2 * log₂ |Bool| = 2` upper bound of `mutualInfo_unitary_onFirst_le`.
example :
    let p := uniformOfFintype (Bool × Bool)
    let U (ab : Bool × Bool) := superdenseEncoding ab.1 ab.2
    mutualInfo (p.bind fun ab =>
      (superdensePOVM.measureDensity
        (((U ab : Matrix Bool Bool ℂ) ⊗ₖ (1 : Matrix Bool Bool ℂ)) * pureState bell *
          ((U ab : Matrix Bool Bool ℂ) ⊗ₖ (1 : Matrix Bool Bool ℂ))ᴴ)
        ((isDensityMatrix_pureState norm_bell).conj_unitary
          (kronecker_mem_unitary (U ab).property (one_mem _)))).map (ab, ·)) = 2 ∧
    mutualInfo (p.bind fun ab =>
      (superdensePOVM.measureDensity
        (((U ab : Matrix Bool Bool ℂ) ⊗ₖ (1 : Matrix Bool Bool ℂ)) * pureState bell *
          ((U ab : Matrix Bool Bool ℂ) ⊗ₖ (1 : Matrix Bool Bool ℂ))ᴴ)
        ((isDensityMatrix_pureState norm_bell).conj_unitary
          (kronecker_mem_unitary (U ab).property (one_mem _)))).map (ab, ·)) ≤
      2 * Real.logb 2 (Fintype.card Bool) := by
  dsimp only
  refine ⟨?_, mutualInfo_unitary_onFirst_le _ _ (isDensityMatrix_pureState norm_bell) _⟩
  simp_rw [measureDensity_superdensePOVM]
  rw [mutualInfo_bind_pure, entropy_uniform, Fintype.card_prod, Fintype.card_bool,
    show ((2 * 2 : ℕ) : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.logb_pow, Real.logb,
    div_self (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne', mul_one, Nat.cast_ofNat]

/-! ### Non-vacuity and tightness of `IsPrivateQuantumChannel` -/

/-- The `2n`-bit quantum one-time pad packaged with a trivial `Unit` ancilla as a
`IsPrivateQuantumChannel`. -/
noncomputable def otpUnitary {α : Type*} [Fintype α] [DecidableEq α]
    (k : (α → Bool) × (α → Bool)) : unitaryGroup ((α → Bool) × Unit) ℂ :=
  ⟨pauliString k.1 k.2 ⊗ₖ (1 : Matrix Unit Unit ℂ),
    kronecker_mem_unitary (pauliString_mem_unitaryGroup k.1 k.2) (one_mem _)⟩

/-- For every finite register `α`, the `2n`-bit quantum one-time pad satisfies
`IsPrivateQuantumChannel` on all unit pure states and achieves the `2n` key-entropy lower bound
with equality. -/
theorem isPrivateQuantumChannel_oneTimePad (α : Type*) [Fintype α] [DecidableEq α] :
    IsPrivateQuantumChannel {ψ : EuclideanSpace ℂ (α → Bool) | ‖ψ‖ = 1}
      (uniformOfFintype ((α → Bool) × (α → Bool))) otpUnitary
      (1 : Matrix Unit Unit ℂ)
      (((2 ^ Fintype.card α : ℂ)⁻¹ • (1 : OneTimePad.Op α)) ⊗ₖ (1 : Matrix Unit Unit ℂ)) := by
  refine ⟨⟨PosSemidef.one, by simp⟩, fun ψ hψ => ?_⟩
  rw [encryptAvg]
  have hterm (k : (α → Bool) × (α → Bool)) :
      (uniformOfFintype ((α → Bool) × (α → Bool)) k).toReal •
          ((otpUnitary k : Matrix ((α → Bool) × Unit) ((α → Bool) × Unit) ℂ) *
            (pureState ψ ⊗ₖ (1 : Matrix Unit Unit ℂ)) *
            (otpUnitary k : Matrix ((α → Bool) × Unit) ((α → Bool) × Unit) ℂ)ᴴ) =
        ((Fintype.card ((α → Bool) × (α → Bool)) : ℂ)⁻¹ •
          OneTimePad.encrypt k (pureState ψ)) ⊗ₖ (1 : Matrix Unit Unit ℂ) := by
    dsimp only [otpUnitary]
    rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, ← mul_kronecker_mul,
      Matrix.mul_one, Matrix.mul_one, ← OneTimePad.encrypt_def, uniformOfFintype_apply,
      ENNReal.toReal_inv, ENNReal.toReal_natCast, ← smul_kronecker]
    ext p q
    simp [Complex.real_smul]
  simp_rw [hterm]
  have hsum_kr (f : (α → Bool) × (α → Bool) → OneTimePad.Op α) :
      (∑ k, f k ⊗ₖ (1 : Matrix Unit Unit ℂ)) = (∑ k, f k) ⊗ₖ (1 : Matrix Unit Unit ℂ) := by
    ext ⟨u, ⟨⟩⟩ ⟨u', ⟨⟩⟩
    simp [Matrix.sum_apply]
  rw [hsum_kr, ← Finset.smul_sum, ← OneTimePad.averageCiphertext_def,
    OneTimePad.averageCiphertext_eq (isDensityMatrix_pureState hψ)]

example (α : Type*) [Fintype α] [DecidableEq α] :
    entropy (uniformOfFintype ((α → Bool) × (α → Bool))) = 2 * (Fintype.card α : ℝ) := by
  rw [entropy_uniform, OneTimePad.card_key, Nat.cast_pow, Nat.cast_ofNat,
    show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, ← pow_mul, Real.logb_pow, Real.logb,
    div_self (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne', mul_one, Nat.cast_mul,
    Nat.cast_ofNat]

/-! ### Model boundaries: basis vs unentangled vs entangled states -/

-- Boundary 1: random bit-flips `X^a` alone (`1` key bit on `Unit → Bool`) DO form a private
-- quantum channel for the computational basis `Set.range ket` (saturating Theorem 5.3 at `1 = 1`),
-- while NO `1`-bit key can hide `unentangledPureStates Unit` (Corollary 5.4 requires `2` bits).
noncomputable def bitFlipOnly (a : Unit → Bool) : unitaryGroup ((Unit → Bool) × Unit) ℂ :=
  ⟨pauliXPow a ⊗ₖ (1 : Matrix Unit Unit ℂ),
    kronecker_mem_unitary (pauliXPow_mem_unitaryGroup a) (one_mem _)⟩

example :
    IsPrivateQuantumChannel (Set.range (ket (ι := Unit → Bool)))
      (uniformOfFintype (Unit → Bool)) bitFlipOnly (1 : Matrix Unit Unit ℂ)
      (((2 : ℂ)⁻¹ • (1 : OneTimePad.Op Unit)) ⊗ₖ (1 : Matrix Unit Unit ℂ)) := by
  refine ⟨⟨PosSemidef.one, by simp⟩, ?_⟩
  rintro _ ⟨x, rfl⟩
  ext ⟨u, ⟨⟩⟩ ⟨u', ⟨⟩⟩
  obtain ⟨bx, rfl⟩ := (Equiv.funUnique Unit Bool).symm.surjective x
  obtain ⟨bu, rfl⟩ := (Equiv.funUnique Unit Bool).symm.surjective u
  obtain ⟨bu', rfl⟩ := (Equiv.funUnique Unit Bool).symm.surjective u'
  rw [encryptAvg]
  simp only [bitFlipOnly, Matrix.sum_apply, Matrix.smul_apply, Matrix.mul_apply,
    conjTranspose_apply, kroneckerMap_apply, Matrix.one_apply, ↓reduceIte, mul_one,
    Fintype.sum_prod_type, Fintype.univ_punit, Finset.sum_singleton, pureState_apply,
    pauliXPow_apply, uniformOfFintype_apply, Fintype.card_fun, Fintype.card_unit,
    Fintype.card_bool, pow_one, Nat.cast_ofNat, ENNReal.toReal_inv, ENNReal.toReal_ofNat,
    Complex.real_smul]
  simp_rw [← (Equiv.funUnique Unit Bool).symm.sum_comp, Fintype.sum_bool]
  cases bx <;> cases bu <;> cases bu'
  all_goals
    simp only [Equiv.funUnique_symm_apply, funext_iff, Unique.forall_iff, Pi.add_apply,
      Bool.add_eq_xor, ket_apply]
    norm_num

example :
    ¬ ∃ (U : (Unit → Bool) → unitaryGroup ((Unit → Bool) × Unit) ℂ)
        (ρ₀ : Matrix ((Unit → Bool) × Unit) ((Unit → Bool) × Unit) ℂ),
      IsPrivateQuantumChannel (unentangledPureStates Unit)
        (uniformOfFintype (Unit → Bool)) U (1 : Matrix Unit Unit ℂ) ρ₀ := by
  rintro ⟨U, ρ₀, h⟩
  have hlow := two_mul_card_le_entropy_of_unentangled h
  rw [Fintype.card_unit, Nat.cast_one, mul_one, entropy_uniform,
    Fintype.card_fun, Fintype.card_unit, Fintype.card_bool, pow_one, Nat.cast_ofNat, Real.logb,
    div_self (Real.log_pos (by norm_num)).ne'] at hlow
  linarith

-- Non-basis product witness via `mem_unentangledPureStates`: `|+⟩^{⊗ n}` with
-- `|+⟩ = (1 / √2) (|0⟩ + |1⟩)` belongs to `unentangledPureStates α`.
example (α : Type*) [Fintype α] :
    let plus : EuclideanSpace ℂ Bool :=
      unitaryEquiv ⟨Gate.hadamardMatrix, Gate.hadamardMatrix_mem_unitaryGroup⟩ (ket false)
    let prodPlus : EuclideanSpace ℂ (α → Bool) := WithLp.toLp 2 fun u => ∏ _i : α, plus.ofLp (u _i)
    prodPlus ∈ unentangledPureStates α := by
  intro plus prodPlus
  rw [mem_unentangledPureStates]
  exact ⟨fun _ => plus, fun _ => by rw [LinearIsometryEquiv.norm_map, norm_ket], fun _ => rfl⟩

-- Boundary 2: the two-qubit Bell state `(1 / √2) (|00⟩ + |11⟩)` is a normalized pure state
-- outside `unentangledPureStates (Fin 2)`, confirming `unentangledPureStates` is a strict subset.
noncomputable def bellFin2 : EuclideanSpace ℂ (Fin 2 → Bool) :=
  (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
    (ket (fun _ : Fin 2 => false) + ket (fun _ : Fin 2 => true))

example : ‖bellFin2‖ = 1 ∧ bellFin2 ∉ unentangledPureStates (Fin 2) := by
  have hne : (fun _ : Fin 2 => false) ≠ (fun _ : Fin 2 => true) := fun h =>
    Bool.false_ne_true (congrFun h 0)
  refine ⟨?_, ?_⟩
  · have hsq : ‖bellFin2‖ ^ 2 = 1 := by
      dsimp only [bellFin2]
      rw [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow,
        Real.sq_sqrt (by norm_num), EuclideanSpace.norm_sq_eq]
      have hterm (f : Fin 2 → Bool) :
          ‖(ket (fun _ : Fin 2 => false) + ket (fun _ : Fin 2 => true)).ofLp f‖ ^ 2 =
            (if f = fun _ => false then (1 : ℝ) else 0) +
              (if f = fun _ => true then 1 else 0) := by
        simp only [WithLp.ofLp_add, Pi.add_apply, ket_apply]
        by_cases hf0 : f = fun _ => false
        · subst hf0; simp [hne]
        · by_cases hf1 : f = fun _ => true
          · subst hf1; simp [hf0]
          · simp [hf0, hf1]
      simp_rw [hterm]
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      norm_num
    exact (sq_eq_one_iff.mp hsq).resolve_right (by linarith [norm_nonneg bellFin2])
  · rw [mem_unentangledPureStates]
    rintro ⟨φ, -, hφ⟩
    have h00 := hφ (fun _ => false)
    have h11 := hφ (fun _ => true)
    have h01 := hφ ![false, true]
    rw [Fin.prod_univ_two] at h00 h11 h01
    have h1 : (![false, true] : Fin 2 → Bool) ≠ fun _ => false := fun h =>
      Bool.false_ne_true (congrFun h 1).symm
    have h2 : (![false, true] : Fin 2 → Bool) ≠ fun _ => true := fun h =>
      Bool.false_ne_true (congrFun h 0)
    simp only [bellFin2, WithLp.ofLp_smul, WithLp.ofLp_add, Pi.smul_apply, Pi.add_apply,
      ket_apply, hne, Ne.symm hne, h1, h2, ↓reduceIte, add_zero, zero_add, smul_eq_mul, mul_one,
      mul_zero, Matrix.cons_val_zero, Matrix.cons_val_one] at h00 h11 h01
    have hprod :
        (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = 0 := by
      calc
        (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
            = ((φ 0).ofLp false * (φ 1).ofLp false) *
                ((φ 0).ofLp true * (φ 1).ofLp true) := by rw [← h00, ← h11]
        _ = ((φ 0).ofLp false * (φ 1).ofLp true) *
              ((φ 0).ofLp true * (φ 1).ofLp false) := by ring
        _ = 0 := by rw [← h01, zero_mul]
    have hhalf : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = (2 : ℂ)⁻¹ := by
      rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]
      norm_num
    rw [hhalf] at hprod
    norm_num at hprod

end CslibFrontierTests.QuantumHolevo
