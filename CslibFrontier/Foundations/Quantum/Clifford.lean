/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Bell
public import CslibFrontier.Foundations.Quantum.Pauli
import CslibFrontier.Foundations.LinearAlgebra.Matrix.UnitaryGroup

/-!
# Weyl–Brauer Clifford observables on `k` qubits

On `k` qubits (`Fin k → Bool`, of dimension `2^k`), inductively tensoring `pauliZ`, `pauliX`, and
`pauliY` produces `2k` pairwise anticommuting Hermitian involutions (`Cslib.Quantum.cliffordGen`).
Contracting the first `m` generators (`k = ⌈m / 2⌉ = (m + 1) / 2`) against any vector
`u ∈ ℝ^m` yields a Hermitian matrix `Cslib.Quantum.cliffordObservable u` satisfying
`(cliffordObservable u)² = ‖u‖² · 1`, hence a `±1` observable whenever `‖u‖ = 1`.

Pairing `cliffordObservable u` on Alice's half and `(cliffordObservable v)ᵀ` on Bob's half of the
maximally entangled state `maxEntangled (Fin ((m + 1) / 2) → Bool)` evaluates to the exact real
inner product `⟪u, v⟫` (`Cslib.Quantum.star_maxEntangled_cliffordObservable`). This is the
Weyl–Brauer / Clifford algebra step realizing Tsirelson's vector correspondence in dimension
`2^⌈m / 2⌉` ([Cirel'son][Cirelson1980];
[Cleve, Høyer, Toner, Watrous, §5.3, Theorem 4][CleveHoyerTonerWatrous2004]).

## Main definitions

* `Cslib.Quantum.pauliY`: the single-qubit Pauli matrix `Y = [[0, -i], [i, 0]]`.
* `Cslib.Quantum.cliffordGen`: `2k` pairwise anticommuting Hermitian involutions on `Fin k → Bool`.
* `Cslib.Quantum.cliffordObservable`: the Hermitian observable `∑_j u_j Γ_j` on `⌈m / 2⌉` qubits.

## Main results

* `Cslib.Quantum.cliffordGen_mul_self`, `Cslib.Quantum.cliffordGen_anticommute`: the Clifford
  relations `Γ_i² = 1` and `Γ_i Γ_j = -Γ_j Γ_i` (`i ≠ j`).
* `Cslib.Quantum.cliffordObservable_mul_self`: unit vectors `‖u‖ = 1` give `±1` observables.
* `Cslib.Quantum.star_maxEntangled_cliffordObservable`:
  `⟨Φ| cliffordObservable u ⊗ (cliffordObservable v)ᵀ |Φ⟩ = ⟪u, v⟫`.

## References

* [B. S. Cirel'son, *Quantum generalizations of Bell's inequality*][Cirelson1980]
* [R. Cleve, P. Høyer, B. Toner, J. Watrous, *Consequences and limits of nonlocal
  strategies*][CleveHoyerTonerWatrous2004]
-/

public section

namespace Cslib.Quantum

open Matrix Finset
open scoped Kronecker

/-! ### The single-qubit Pauli matrix `Y` -/

/-- The **Pauli matrix** `Y = [[0, -i], [i, 0]]`, indexed by `Bool` (`false` for `0`, `true` for
`1`). -/
@[expose] noncomputable def pauliY : Matrix Bool Bool ℂ :=
  fun b c => if b = c then 0 else if b then Complex.I else -Complex.I

@[simp] theorem pauliY_apply (b c : Bool) :
    pauliY b c = if b = c then 0 else if b then Complex.I else -Complex.I :=
  rfl

theorem pauliY_isHermitian : pauliY.IsHermitian := by
  ext b c
  cases b <;> cases c <;> simp [conjTranspose_apply]

theorem pauliY_mul_self : pauliY * pauliY = 1 := by
  ext b c
  cases b <;> cases c <;> simp [Matrix.mul_apply]

theorem pauliY_mem_unitaryGroup : pauliY ∈ unitaryGroup Bool ℂ :=
  pauliY_isHermitian.mem_unitaryGroup_of_mul_self pauliY_mul_self

theorem pauliZ_mul_pauliY : pauliZ * pauliY = -(pauliY * pauliZ) := by
  ext b c
  cases b <;> cases c <;> simp [Matrix.mul_apply]

theorem pauliX_mul_pauliY : pauliX * pauliY = -(pauliY * pauliX) := by
  ext b c
  cases b <;> cases c <;> simp [Matrix.mul_apply]

/-! ### Recursive `2k`-generator Clifford system on `k` qubits -/

private theorem neg_kronecker_left {m n p q : Type*} (A : Matrix m n ℂ) (B : Matrix p q ℂ) :
    (-A) ⊗ₖ B = -(A ⊗ₖ B) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  exact neg_mul _ _

private theorem neg_kronecker_right {m n p q : Type*} (A : Matrix m n ℂ) (B : Matrix p q ℂ) :
    A ⊗ₖ (-B) = -(A ⊗ₖ B) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  exact mul_neg _ _

private noncomputable def cliffordStep {m : ℕ} {α : Type*} [DecidableEq α]
    (G : Fin m → Matrix α α ℂ) (i : Fin (m + 2)) : Matrix (Bool × α) (Bool × α) ℂ :=
  if hlt : i.val < m then pauliZ ⊗ₖ G ⟨i.val, hlt⟩
  else if i.val = m then pauliX ⊗ₖ (1 : Matrix α α ℂ)
  else pauliY ⊗ₖ (1 : Matrix α α ℂ)

private theorem isHermitian_cliffordStep {m : ℕ} {α : Type*} [DecidableEq α]
    {G : Fin m → Matrix α α ℂ} (hH : ∀ i, (G i).IsHermitian) (i : Fin (m + 2)) :
    (cliffordStep G i).IsHermitian := by
  unfold cliffordStep
  split_ifs with hlt heq
  · rw [IsHermitian, conjTranspose_kronecker, pauliZ_isHermitian.eq, (hH _).eq]
  · rw [IsHermitian, conjTranspose_kronecker, pauliX_isHermitian.eq, conjTranspose_one]
  · rw [IsHermitian, conjTranspose_kronecker, pauliY_isHermitian.eq, conjTranspose_one]

private theorem cliffordStep_mul_self {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    {G : Fin m → Matrix α α ℂ} (hsq : ∀ i, G i * G i = 1) (i : Fin (m + 2)) :
    cliffordStep G i * cliffordStep G i = 1 := by
  unfold cliffordStep
  split_ifs with hlt heq
  · rw [← mul_kronecker_mul, pauliZ_mul_self, hsq, one_kronecker_one]
  · rw [← mul_kronecker_mul, pauliX_mul_self, Matrix.mul_one, one_kronecker_one]
  · rw [← mul_kronecker_mul, pauliY_mul_self, Matrix.mul_one, one_kronecker_one]

private theorem cliffordStep_anticommute {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    {G : Fin m → Matrix α α ℂ}
    (hanti : ∀ {i j : Fin m}, i ≠ j → G i * G j = -(G j * G i))
    {i j : Fin (m + 2)} (hij : i ≠ j) :
    cliffordStep G i * cliffordStep G j = -(cliffordStep G j * cliffordStep G i) := by
  have hij_val : i.val ≠ j.val := fun h => hij (Fin.ext h)
  by_cases hi1 : i.val < m
  · by_cases hj1 : j.val < m
    · have hne : (⟨i.val, hi1⟩ : Fin m) ≠ ⟨j.val, hj1⟩ := fun h => hij_val (Fin.mk.inj h)
      simp only [cliffordStep, hi1, hj1, ↓reduceDIte]
      rw [← mul_kronecker_mul, ← mul_kronecker_mul, pauliZ_mul_self, hanti hne,
        neg_kronecker_right]
    · by_cases hj2 : j.val = m
      · simp only [cliffordStep, hi1, hj2, lt_irrefl, ↓reduceDIte, ↓reduceIte]
        rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
          pauliZ_mul_pauliX, neg_kronecker_left]
      · simp only [cliffordStep, hi1, hj1, hj2, ↓reduceDIte, ↓reduceIte]
        rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
          pauliZ_mul_pauliY, neg_kronecker_left]
  · by_cases hi2 : i.val = m
    · by_cases hj1 : j.val < m
      · have hZX : pauliX * pauliZ = -(pauliZ * pauliX) := by rw [pauliZ_mul_pauliX, neg_neg]
        simp only [cliffordStep, hi2, lt_irrefl, hj1, ↓reduceDIte, ↓reduceIte]
        rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
          hZX, neg_kronecker_left]
      · have hj2 : j.val ≠ m := fun h => hij_val (hi2.trans h.symm)
        simp only [cliffordStep, hi2, lt_irrefl, hj1, hj2, ↓reduceDIte, ↓reduceIte]
        rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one,
          pauliX_mul_pauliY, neg_kronecker_left]
    · by_cases hj1 : j.val < m
      · have hZY : pauliY * pauliZ = -(pauliZ * pauliY) := by rw [pauliZ_mul_pauliY, neg_neg]
        simp only [cliffordStep, hi1, hi2, hj1, ↓reduceDIte, ↓reduceIte]
        rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
          hZY, neg_kronecker_left]
      · have hj2 : j.val = m := by omega
        have hYX : pauliY * pauliX = -(pauliX * pauliY) := by rw [pauliX_mul_pauliY, neg_neg]
        simp only [cliffordStep, hi1, hi2, hj2, lt_irrefl, ↓reduceDIte, ↓reduceIte]
        rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one,
          hYX, neg_kronecker_left]

/-- Splitting an `(k + 1)`-qubit basis string into its head bit and `k`-qubit tail. -/
private def qubitConsEquiv (k : ℕ) : (Fin (k + 1) → Bool) ≃ Bool × (Fin k → Bool) :=
  (Fin.consEquiv (fun _ : Fin (k + 1) => Bool)).symm

/-- **`2k` pairwise anticommuting Hermitian involutions** on `k` qubits (`Fin k → Bool`). -/
noncomputable def cliffordGen :
    (k : ℕ) → Fin (2 * k) → Matrix (Fin k → Bool) (Fin k → Bool) ℂ
  | 0 => Fin.elim0
  | k + 1 => fun i =>
    submatrix (cliffordStep (cliffordGen k) ⟨i.val, by omega⟩) (qubitConsEquiv k) (qubitConsEquiv k)

theorem isHermitian_cliffordGen (k : ℕ) (i : Fin (2 * k)) :
    (cliffordGen k i).IsHermitian := by
  induction k with
  | zero => exact i.elim0
  | succ k ih =>
    simp only [cliffordGen]
    rw [IsHermitian, conjTranspose_submatrix, (isHermitian_cliffordStep ih _).eq]

theorem cliffordGen_mul_self (k : ℕ) (i : Fin (2 * k)) :
    cliffordGen k i * cliffordGen k i = 1 := by
  induction k with
  | zero => exact i.elim0
  | succ k ih =>
    simp only [cliffordGen]
    rw [submatrix_mul_equiv _ _ (qubitConsEquiv k) (qubitConsEquiv k) (qubitConsEquiv k),
      cliffordStep_mul_self ih, submatrix_one_equiv]

theorem cliffordGen_anticommute (k : ℕ) {i j : Fin (2 * k)} (hij : i ≠ j) :
    cliffordGen k i * cliffordGen k j = -(cliffordGen k j * cliffordGen k i) := by
  induction k with
  | zero => exact i.elim0
  | succ k ih =>
    have hij' : (⟨i.val, by omega⟩ : Fin (2 * k + 2)) ≠ ⟨j.val, by omega⟩ :=
      fun h => hij (Fin.ext (Fin.mk.inj h))
    simp only [cliffordGen]
    rw [submatrix_mul_equiv _ _ (qubitConsEquiv k) (qubitConsEquiv k) (qubitConsEquiv k),
      submatrix_mul_equiv _ _ (qubitConsEquiv k) (qubitConsEquiv k) (qubitConsEquiv k),
      cliffordStep_anticommute ih hij', submatrix_neg]
    rfl

private theorem trace_mul_eq_zero_of_anticommute {α : Type*} [Fintype α] {A B : Matrix α α ℂ}
    (h : A * B = -(B * A)) : (A * B).trace = 0 := by
  have htr : (A * B).trace = -(A * B).trace := by
    calc
      (A * B).trace = (-(B * A)).trace := by rw [h]
      _ = -(B * A).trace := trace_neg _
      _ = -(A * B).trace := by rw [trace_mul_comm]
  linear_combination (1 / 2 : ℂ) * htr

theorem trace_cliffordGen_mul (k : ℕ) (i j : Fin (2 * k)) :
    (cliffordGen k i * cliffordGen k j).trace =
      if i = j then (Fintype.card (Fin k → Bool) : ℂ) else 0 := by
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceIte, cliffordGen_mul_self, trace_one]
  · simp only [hij, ↓reduceIte]
    exact trace_mul_eq_zero_of_anticommute (cliffordGen_anticommute k hij)

/-! ### Real-vector observables and maximally entangled inner-product pairing -/

/-- The Hermitian Clifford observable `∑_{j < m} u_j Γ_j` on `⌈m / 2⌉ = (m + 1) / 2` qubits
associated with a real vector `u ∈ ℝ^m`. -/
@[expose] noncomputable def cliffordObservable {m : ℕ} (u : EuclideanSpace ℝ (Fin m)) :
    Matrix (Fin ((m + 1) / 2) → Bool) (Fin ((m + 1) / 2) → Bool) ℂ :=
  ∑ j : Fin m, (u.ofLp j : ℂ) • cliffordGen ((m + 1) / 2) ⟨j.val, by omega⟩

theorem isHermitian_cliffordObservable {m : ℕ} (u : EuclideanSpace ℝ (Fin m)) :
    (cliffordObservable u).IsHermitian := by
  rw [IsHermitian, cliffordObservable, conjTranspose_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, (isHermitian_cliffordGen _ _).eq]

theorem cliffordObservable_mul_self_eq_norm_sq {m : ℕ} (u : EuclideanSpace ℝ (Fin m)) :
    cliffordObservable u * cliffordObservable u = ((‖u‖ ^ 2 : ℝ) : ℂ) • 1 := by
  let k := (m + 1) / 2
  let G (j : Fin m) : Matrix (Fin k → Bool) (Fin k → Bool) ℂ :=
    cliffordGen k ⟨j.val, by omega⟩
  have hG_sq (j : Fin m) : G j * G j = 1 := cliffordGen_mul_self k _
  have hG_anti {i j : Fin m} (hij : i ≠ j) : G i * G j = -(G j * G i) :=
    cliffordGen_anticommute k (fun h => hij (Fin.ext (Fin.mk.inj h)))
  let M := cliffordObservable u
  have hMM1 : M * M = ∑ i : Fin m, ∑ j : Fin m, ((u.ofLp i * u.ofLp j : ℝ) : ℂ) • (G i * G j) := by
    dsimp only [M, cliffordObservable]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Complex.ofReal_mul]
  have hMM2 : M * M = ∑ i : Fin m, ∑ j : Fin m, ((u.ofLp i * u.ofLp j : ℝ) : ℂ) • (G j * G i) := by
    rw [hMM1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm (u.ofLp j) (u.ofLp i)]
  have hdouble : M * M + M * M = (2 : ℂ) • (((‖u‖ ^ 2 : ℝ) : ℂ) • 1) := by
    conv_lhs =>
      lhs
      rw [hMM1]
    conv_lhs =>
      rhs
      rw [hMM2]
    rw [← Finset.sum_add_distrib]
    have hinner (i : Fin m) :
        (∑ j : Fin m, (((u.ofLp i * u.ofLp j : ℝ) : ℂ) • (G i * G j) +
            ((u.ofLp i * u.ofLp j : ℝ) : ℂ) • (G j * G i))) =
          ((u.ofLp i ^ 2 : ℝ) : ℂ) • ((2 : ℂ) • 1) := by
      have hterm (j : Fin m) :
          (((u.ofLp i * u.ofLp j : ℝ) : ℂ) • (G i * G j) +
              ((u.ofLp i * u.ofLp j : ℝ) : ℂ) • (G j * G i)) =
            if j = i then ((u.ofLp i ^ 2 : ℝ) : ℂ) • ((2 : ℂ) • 1) else 0 := by
        by_cases hij : j = i
        · subst hij
          simp only [↓reduceIte, hG_sq, ← sq, ← smul_add, two_smul]
        · simp only [hij, ↓reduceIte, hG_anti (Ne.symm hij), smul_neg, neg_add_cancel]
      rw [Finset.sum_eq_single i (fun j _ hj => by rw [hterm j, ite_eq_right_iff.mpr (by tauto)])
        (fun hi => absurd (Finset.mem_univ i) hi), hterm i]
      simp only [eq_self, ↓reduceIte]
    have hsum_i :
        (∑ i : Fin m, ((∑ j : Fin m, ((u.ofLp i * u.ofLp j : ℝ) : ℂ) • (G i * G j)) +
            ∑ j : Fin m, ((u.ofLp i * u.ofLp j : ℝ) : ℂ) • (G j * G i))) =
          ∑ i : Fin m, ((u.ofLp i ^ 2 : ℝ) : ℂ) • ((2 : ℂ) • 1) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      exact hinner i
    rw [hsum_i, ← Finset.sum_smul]
    rw [EuclideanSpace.norm_sq_eq]
    have hnorm : (∑ i : Fin m, ((u.ofLp i ^ 2 : ℝ) : ℂ)) =
        ((∑ i : Fin m, ‖u.ofLp i‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Real.norm_eq_abs, sq_abs]
    rw [hnorm, smul_comm]
  calc
    M * M = (2⁻¹ : ℂ) • (M * M + M * M) := by rw [← two_smul ℂ (M * M), smul_smul]; norm_num
    _ = ((‖u‖ ^ 2 : ℝ) : ℂ) • 1 := by rw [hdouble, smul_smul]; norm_num

/-- When `u` is a real unit vector, `cliffordObservable u` squares to the identity. -/
theorem cliffordObservable_mul_self {m : ℕ} {u : EuclideanSpace ℝ (Fin m)} (hu : ‖u‖ = 1) :
    cliffordObservable u * cliffordObservable u = 1 := by
  rw [cliffordObservable_mul_self_eq_norm_sq, hu, one_pow, Complex.ofReal_one, one_smul]

theorem isHermitian_transpose_cliffordObservable {m : ℕ} (v : EuclideanSpace ℝ (Fin m)) :
    (cliffordObservable v)ᵀ.IsHermitian := by
  ext a b
  simpa only [conjTranspose_apply, transpose_apply] using
    congrFun (congrFun (isHermitian_cliffordObservable v).eq b) a

theorem transpose_cliffordObservable_mul_self {m : ℕ} {v : EuclideanSpace ℝ (Fin m)}
    (hv : ‖v‖ = 1) :
    (cliffordObservable v)ᵀ * (cliffordObservable v)ᵀ = 1 := by
  rw [← transpose_mul, cliffordObservable_mul_self hv, transpose_one]

/-- Trace pairing of two Clifford observables equals `2^⌈m / 2⌉` times the real inner product. -/
theorem trace_cliffordObservable_mul {m : ℕ} (u v : EuclideanSpace ℝ (Fin m)) :
    (cliffordObservable u * cliffordObservable v).trace =
      (inner ℝ u v : ℂ) * (Fintype.card (Fin ((m + 1) / 2) → Bool) : ℂ) := by
  let k := (m + 1) / 2
  unfold cliffordObservable
  rw [Finset.sum_mul, trace_sum]
  have hrow (i : Fin m) :
      ((∑ j : Fin m, ((u.ofLp i : ℂ) • cliffordGen k ⟨i.val, by omega⟩) *
          ((v.ofLp j : ℂ) • cliffordGen k ⟨j.val, by omega⟩))).trace =
        ((u.ofLp i * v.ofLp i : ℝ) : ℂ) * (Fintype.card (Fin k → Bool) : ℂ) := by
    rw [trace_sum]
    have hterm (j : Fin m) :
        (((u.ofLp i : ℂ) • cliffordGen k ⟨i.val, by omega⟩) *
            ((v.ofLp j : ℂ) • cliffordGen k ⟨j.val, by omega⟩)).trace =
          if j = i then ((u.ofLp i * v.ofLp i : ℝ) : ℂ) * (Fintype.card (Fin k → Bool) : ℂ)
          else 0 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, trace_smul, smul_eq_mul,
        trace_cliffordGen_mul]
      by_cases hij : j = i
      · subst hij
        simp only [↓reduceIte, Complex.ofReal_mul]
      · have hne : (⟨i.val, by omega⟩ : Fin (2 * k)) ≠ ⟨j.val, by omega⟩ :=
          fun h => hij (Fin.ext (Fin.mk.inj h)).symm
        simp only [hne, hij, ↓reduceIte, mul_zero]
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [hterm j, ite_eq_right_iff.mpr (by tauto)])
      (fun hi => absurd (Finset.mem_univ i) hi), hterm i]
    simp only [eq_self, ↓reduceIte]
  -- Distribute `(u_i • G_i) * ∑ j, ...` inside the outer sum first:
  have hdist (i : Fin m) :
      (((u.ofLp i : ℂ) • cliffordGen k ⟨i.val, by omega⟩) *
          ∑ j : Fin m, (v.ofLp j : ℂ) • cliffordGen k ⟨j.val, by omega⟩).trace =
        ((u.ofLp i * v.ofLp i : ℝ) : ℂ) * (Fintype.card (Fin k → Bool) : ℂ) := by
    rw [Finset.mul_sum]
    exact hrow i
  have hsum_dist :
      (∑ i : Fin m, (((u.ofLp i : ℂ) • cliffordGen ((m + 1) / 2) ⟨i.val, by omega⟩) *
          ∑ j : Fin m, (v.ofLp j : ℂ) • cliffordGen ((m + 1) / 2) ⟨j.val, by omega⟩).trace) =
        ∑ i : Fin m, ((u.ofLp i * v.ofLp i : ℝ) : ℂ) * (Fintype.card (Fin k → Bool) : ℂ) :=
    Finset.sum_congr rfl fun i _ => hdist i
  rw [hsum_dist, ← Finset.sum_mul, PiLp.inner_apply, Complex.ofReal_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.inner_apply, conj_trivial, mul_comm (v.ofLp i) (u.ofLp i)]

/-- Pairing `cliffordObservable u` with `(cliffordObservable v)ᵀ` on the maximally entangled state
recovers `(inner ℝ u v : ℂ)` exactly. -/
theorem star_maxEntangled_cliffordObservable {m : ℕ} (u v : EuclideanSpace ℝ (Fin m)) :
    let ι := Fin ((m + 1) / 2) → Bool
    star (maxEntangled ι).ofLp ⬝ᵥ
        (((cliffordObservable u) ⊗ₖ (cliffordObservable v)ᵀ) *ᵥ (maxEntangled ι).ofLp) =
      (inner ℝ u v : ℂ) := by
  intro ι
  rw [star_maxEntangled_dotProduct_kronecker_mulVec_eq_trace, ← transpose_mul, trace_transpose,
    trace_cliffordObservable_mul, real_inner_comm]
  have hcard : (Fintype.card ι : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := ι)
  exact mul_div_cancel_right₀ _ hcard

end Cslib.Quantum
