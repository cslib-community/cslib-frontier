/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Int.Radix
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.IntegerKernel
public import CslibFrontier.GameTheory.Bimatrix.BestResponsePolytope
public import CslibFrontier.GameTheory.Bimatrix.ShapleyOrientation
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Cramer
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Perturbed best-response polytopes, integer bases, and exact rational Nash recovery

This module supplies the quantitative and polyhedral infrastructure turning arbitrary rational
bimatrix games into nondegenerate integer-matrix Lemke–Howson instances whose nonzero completely
labelled vertices yield exact rational Nash equilibria.

Following [vonStengel2007, Section 3.6], for positive integer payoff matrices
`A B : Matrix (Fin m) (Fin n) ℤ` with entries in `[1, H]`, we perturb the right-hand sides of
the scaled best-response polytopes `P_ε = {x ≥ 0 | Bᵀ x ≤ K^n + K^(n-1-j)}` and
`Q_ε = {y ≥ 0 | A y ≤ K^m + K^(m-1-i)}` with `K = 2 ^ bitBound m n H`.

## Main definitions

* `Cslib.GameTheory.BimatrixGame.bitBound`: explicit polynomial bit bound `E` such that `K = 2 ^ E`
  makes `(P_ε, Q_ε)` nondegenerate and supports exact unperturbed Nash extraction.
* `Cslib.GameTheory.BimatrixGame.intMatP`, `Cslib.GameTheory.BimatrixGame.intMatQ`,
  `Cslib.GameTheory.BimatrixGame.pertRhsPInt`, `Cslib.GameTheory.BimatrixGame.pertRhsQInt`:
  integral constraint matrices and perturbed right-hand sides.
* `Cslib.GameTheory.BimatrixGame.IsFeasibleBasis`: pure integer Cramer feasibility predicate for
  `k`-element tight bases.
* `Cslib.GameTheory.BimatrixGame.cramerVec`, `Cslib.GameTheory.BimatrixGame.basisSignNum`:
  signed Cramer numerator vector for an integer basis system.

## Main results

* `Cslib.GameTheory.BimatrixGame.isNash_smul`: positive scaling invariance of `IsNash`.
* `Cslib.GameTheory.BimatrixGame.isNondegenerateSystem_pertP`,
  `Cslib.GameTheory.BimatrixGame.isNondegenerateSystem_pertQ`: nondegeneracy of `(P_ε, Q_ε)` over
  every ordered field (`ℚ`, `ℝ`) whenever `kernelVecBound` is below `K`.
* `Cslib.GameTheory.BimatrixGame.isFeasibleBasis_iff_ratBasisSol_le`,
  `Cslib.GameTheory.BimatrixGame.isVertex_ratBasisSol_of_isFeasibleBasis`,
  `Cslib.GameTheory.BimatrixGame.exists_isFeasibleBasis_of_isVertex`: equivalence between integer
  feasible bases and vertices of `(P_ε, Q_ε)`.
* `Cslib.GameTheory.BimatrixGame.isNash_extractNum`: any nonzero completely labelled basis pair of
  `(P_ε, Q_ε)` extracts an exact rational Nash equilibrium of `⟨A, B⟩`.

## References

* [B. von Stengel, *Equilibrium computation for two-player games in strategic and extensive
  form*][vonStengel2007], Sections 3.5–3.6
-/

public section

open Finset Matrix

namespace Cslib.GameTheory.BimatrixGame

section Scaling

variable {M N : Type*} [Fintype M] [Fintype N]

/-- Positive scalar multiplication of both payoff matrices preserves `IsNash`. -/
theorem isNash_smul {D : ℝ} (hD : 0 < D) (G : BimatrixGame M N) (x : M → ℝ) (y : N → ℝ) :
    ({ A := D • G.A, B := D • G.B } : BimatrixGame M N).IsNash x y ↔ G.IsNash x y := by
  simp only [isNash_iff, isBestResponse₁_iff, isBestResponse₂_iff, isPureBestResponse₁_iff,
    isPureBestResponse₂_iff, Matrix.smul_mulVec, Matrix.vecMul_smul, Pi.smul_apply, smul_eq_mul,
    mul_le_mul_iff_right₀ hD]

end Scaling

section BitBound

/-- Explicit polynomial exponent `E` so that `2 ^ E` suffices for both nondegeneracy and exact
unperturbed Nash extraction on positive integer `m × n` games bounded by `H`. -/
@[expose] def bitBound (m n H : ℕ) : ℕ :=
  4 * (m + n) * (m + n + Nat.log 2 H + 3)

private lemma factorial_le_two_pow_sq (k : ℕ) : k.factorial ≤ 2 ^ (k ^ 2) :=
  (Nat.factorial_le_pow k).trans <| (Nat.pow_le_pow_left Nat.lt_two_pow_self.le k).trans_eq <|
    by rw [← pow_mul, sq]

/-- Strict bit bound dominating `kernelVecBound m H * (n + 1)`. -/
theorem kernelVecBound_mul_lt_two_pow_bitBound {m n H : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Matrix.kernelVecBound m H * (n + 1) < 2 ^ bitBound m n H := by
  set L := Nat.log 2 H + 1
  set s := m + n
  have hHL : H ≤ 2 ^ L := (Nat.lt_pow_succ_log_self (by decide) H).le
  have hprod : (m + 1) * H ≤ 2 ^ (s + L + 1) :=
    (Nat.mul_le_mul ((by omega : m + 1 ≤ s + 1).trans Nat.lt_two_pow_self.le) hHL).trans_eq <| by
      rw [← pow_add, show s + 1 + L = s + L + 1 by omega]
  have hbase : m * ((m + 1) * H) ^ 2 + 1 ≤ 2 ^ (3 * s + 2 * L + 3) := calc
    m * ((m + 1) * H) ^ 2 + 1
        ≤ 2 ^ s * (2 ^ (s + L + 1)) ^ 2 + 1 := by
          gcongr; exact (Nat.le_add_right m n).trans Nat.lt_two_pow_self.le
    _ = 2 ^ (3 * s + 2 * L + 2) + 1 := by
          rw [← pow_mul, ← pow_add]; congr 2; ring
    _ ≤ 2 ^ (3 * s + 2 * L + 2) + 2 ^ (3 * s + 2 * L + 2) :=
          Nat.add_le_add_left Nat.one_le_two_pow _
    _ = 2 ^ (3 * s + 2 * L + 3) := by rw [pow_succ]; ring
  have hpow : (m * ((m + 1) * H) ^ 2 + 1) ^ m ≤ 2 ^ (s * (3 * s + 2 * L + 3)) :=
    (Nat.pow_le_pow_left hbase m).trans <| by
      rw [← pow_mul, mul_comm _ m]
      exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (Nat.le_add_right m n))
  have hexp : s ^ 2 + s * (3 * s + 2 * L + 3) + s < bitBound m n H := by
    have : bitBound m n H = 4 * s * (s + L + 2) := by
      simp only [bitBound, s, L]; ring
    nlinarith [show 1 ≤ L by omega, show 2 ≤ s by omega]
  calc Matrix.kernelVecBound m H * (n + 1)
      ≤ 2 ^ (s ^ 2) * 2 ^ (s * (3 * s + 2 * L + 3)) * 2 ^ s := by
        refine Nat.mul_le_mul (Nat.mul_le_mul
          ((Nat.factorial_le (Nat.le_add_right m n)).trans (factorial_le_two_pow_sq s)) hpow)
          ((by omega : n + 1 ≤ s).trans Nat.lt_two_pow_self.le)
    _ = 2 ^ (s ^ 2 + s * (3 * s + 2 * L + 3) + s) := by rw [← pow_add, ← pow_add]
    _ < 2 ^ bitBound m n H := Nat.pow_lt_pow_right (by decide) hexp

/-- Symmetric strict bit bound dominating `kernelVecBound n H * (m + 1)`. -/
theorem kernelVecBound_mul_lt_two_pow_bitBound_symm {m n H : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Matrix.kernelVecBound n H * (m + 1) < 2 ^ bitBound m n H := by
  simpa only [bitBound, Nat.add_comm n m] using
    kernelVecBound_mul_lt_two_pow_bitBound (H := H) hn hm

/-- Strict Cramer rounding bound for player 1 (`m`) under `K = 2 ^ bitBound m n H`. -/
theorem cramerScale_lt_two_pow_bitBound {m n H : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (m.factorial * H ^ m) * (1 + m * m.factorial * H ^ (m + 1)) < 2 ^ bitBound m n H := by
  set L := Nat.log 2 H + 1
  set s := m + n
  have hHL : H ≤ 2 ^ L := (Nat.lt_pow_succ_log_self (by decide) H).le
  have hfac : m.factorial ≤ 2 ^ (s ^ 2) :=
    (Nat.factorial_le (Nat.le_add_right m n)).trans (factorial_le_two_pow_sq s)
  have hpowH (k t : ℕ) (hk : k ≤ t) : H ^ k ≤ 2 ^ (t * L) :=
    (Nat.pow_le_pow_left hHL k).trans <| by
      rw [← pow_mul, mul_comm L k]
      exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right L hk)
  have hright : 1 + m * m.factorial * H ^ (m + 1) ≤ 2 ^ (s + s ^ 2 + (s + 1) * L + 1) := by
    have hm' : m * m.factorial * H ^ (m + 1) ≤ 2 ^ (s + s ^ 2 + (s + 1) * L) :=
      (Nat.mul_le_mul (Nat.mul_le_mul ((Nat.le_add_right m n).trans Nat.lt_two_pow_self.le) hfac)
        (hpowH (m + 1) (s + 1) (by omega))).trans_eq (by rw [← pow_add, ← pow_add])
    exact (Nat.add_le_add (Nat.one_le_two_pow (n := s + s ^ 2 + (s + 1) * L)) hm').trans_eq
      (by rw [← two_mul, ← pow_succ'])
  have hexp : s ^ 2 + s * L + (s + s ^ 2 + (s + 1) * L + 1) < bitBound m n H := by
    have : bitBound m n H = 4 * s * (s + L + 2) := by
      simp only [bitBound, s, L]; ring
    nlinarith [show 1 ≤ L by omega, show 2 ≤ s by omega]
  calc (m.factorial * H ^ m) * (1 + m * m.factorial * H ^ (m + 1))
      ≤ (2 ^ (s ^ 2) * 2 ^ (s * L)) * 2 ^ (s + s ^ 2 + (s + 1) * L + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul hfac (hpowH m s (Nat.le_add_right m n))) hright
    _ = 2 ^ (s ^ 2 + s * L + (s + s ^ 2 + (s + 1) * L + 1)) := by rw [← pow_add, ← pow_add]
    _ < 2 ^ bitBound m n H := Nat.pow_lt_pow_right (by decide) hexp

/-- Symmetric strict Cramer rounding bound for player 2 (`n`) under `K = 2 ^ bitBound m n H`. -/
theorem cramerScale_lt_two_pow_bitBound_symm {m n H : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (n.factorial * H ^ n) * (1 + n * n.factorial * H ^ (n + 1)) < 2 ^ bitBound m n H := by
  simpa only [bitBound, Nat.add_comm n m] using cramerScale_lt_two_pow_bitBound (H := H) hn hm

end BitBound

section Polytopes

/-- Integer constraint matrix `[-I_m; Bᵀ]` for best-response polytope `P`. -/
@[expose] def intMatP {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℤ) :
    Matrix (Fin m ⊕ Fin n) (Fin m) ℤ :=
  Matrix.fromRows (-1) Bᵀ

/-- Integer constraint matrix `[A; -I_n]` for best-response polytope `Q`. -/
@[expose] def intMatQ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    Matrix (Fin m ⊕ Fin n) (Fin n) ℤ :=
  Matrix.fromRows A (-1)

/-- Unperturbed integer right-hand side `[0; 1]` for `P`. -/
@[expose] def intRhsP (m n : ℕ) : Fin m ⊕ Fin n → ℤ :=
  Sum.elim 0 1

/-- Unperturbed integer right-hand side `[1; 0]` for `Q`. -/
@[expose] def intRhsQ (m n : ℕ) : Fin m ⊕ Fin n → ℤ :=
  Sum.elim 1 0

/-- Perturbed integer right-hand side `[0; K^n + K^(n-1-j)]` for `P_ε`. -/
@[expose] def pertRhsPInt (m n : ℕ) (K : ℤ) : Fin m ⊕ Fin n → ℤ :=
  Sum.elim 0 (fun j => K ^ n + K ^ (n - 1 - j.1))

/-- Perturbed integer right-hand side `[K^m + K^(m-1-i); 0]` for `Q_ε`. -/
@[expose] def pertRhsQInt (m n : ℕ) (K : ℤ) : Fin m ⊕ Fin n → ℤ :=
  Sum.elim (fun i => K ^ m + K ^ (m - 1 - i.1)) 0

@[simp]
theorem intMatP_inl {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℤ) (i i' : Fin m) :
    intMatP B (.inl i) i' = if i = i' then -1 else 0 := by
  simp only [intMatP, Matrix.fromRows_apply_inl, Matrix.neg_apply, Matrix.one_apply]
  split_ifs <;> simp

@[simp]
theorem intMatP_inr {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℤ) (j : Fin n) (i : Fin m) :
    intMatP B (.inr j) i = B i j := by
  simp [intMatP]

@[simp]
theorem intMatQ_inl {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (i : Fin m) (j : Fin n) :
    intMatQ A (.inl i) j = A i j := by
  simp [intMatQ]

@[simp]
theorem intMatQ_inr {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (j j' : Fin n) :
    intMatQ A (.inr j) j' = if j = j' then -1 else 0 := by
  simp only [intMatQ, Matrix.fromRows_apply_inr, Matrix.neg_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem intMatP_map_eq_matP {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℤ) :
    (intMatP B).map (Int.cast : ℤ → ℝ) =
      ({ A := A.map Int.cast, B := B.map Int.cast } : BimatrixGame (Fin m) (Fin n)).matP := by
  let G : BimatrixGame (Fin m) (Fin n) := { A := A.map Int.cast, B := B.map Int.cast }
  refine Matrix.ext fun r c => ?_
  have hcol := congrFun (show ((intMatP B).map (Int.cast : ℤ → ℝ)) *ᵥ Pi.single c 1 =
      G.matP *ᵥ Pi.single c 1 from funext fun r' => by
    cases r' with
    | inl i =>
      rw [G.matP_mulVec_inl]
      simp [mulVec, dotProduct, intMatP_inl, Pi.single_apply, eq_comm, apply_ite]
    | inr j =>
      rw [G.matP_mulVec_inr]
      simp [mulVec, dotProduct, vecMul, intMatP_inr, Pi.single_apply, G]) r
  simpa only [mulVec_single, Pi.smul_apply, op_smul_eq_mul, mul_one, col_apply] using hcol

theorem intMatQ_map_eq_matQ {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℤ) :
    (intMatQ A).map (Int.cast : ℤ → ℝ) =
      ({ A := A.map Int.cast, B := B.map Int.cast } : BimatrixGame (Fin m) (Fin n)).matQ := by
  let G : BimatrixGame (Fin m) (Fin n) := { A := A.map Int.cast, B := B.map Int.cast }
  rw [G.matQ_eq_submatrix_swap_matP]
  have hP := intMatP_map_eq_matP Bᵀ Aᵀ
  have hswap : G.swap = { A := Bᵀ.map Int.cast, B := Aᵀ.map Int.cast } :=
    BimatrixGame.swap_mk _ _
  ext r c
  cases r <;> simp [intMatQ, intMatP, hswap, ← hP]

/-- Swapping `Sum.inl` and `Sum.inr` turns `intMatQ A` into `intMatP Aᵀ`. -/
theorem intMatQ_submatrix_sumComm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    (intMatQ A).submatrix (Equiv.sumComm (Fin n) (Fin m)) id = intMatP Aᵀ := by
  ext r c
  cases r <;> simp [intMatQ, intMatP]

/-- Swapping `Sum.inl` and `Sum.inr` turns `pertRhsQInt m n K` into `pertRhsPInt n m K`. -/
theorem pertRhsQInt_comp_sumComm (m n : ℕ) (K : ℤ) :
    pertRhsQInt m n K ∘ Equiv.sumComm (Fin n) (Fin m) = pertRhsPInt n m K := by
  funext r
  cases r <;> rfl

private lemma intRhsQ_comp_sumComm (m n : ℕ) :
    intRhsQ m n ∘ Equiv.sumComm (Fin n) (Fin m) = intRhsP n m := by
  funext r
  cases r <;> rfl

private lemma intMatQ_map_submatrix_sumComm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    {K : Type*} [IntCast K] :
    ((intMatQ A).map (Int.cast : ℤ → K)).submatrix (Equiv.sumComm (Fin n) (Fin m)) id =
      (intMatP Aᵀ).map Int.cast := by
  rw [← intMatQ_submatrix_sumComm A]
  rfl

private lemma pertRhsQInt_cast_comp_sumComm (m n : ℕ) (K_B : ℤ) {K : Type*} [IntCast K] :
    (fun r => (pertRhsQInt m n K_B r : K)) ∘ Equiv.sumComm (Fin n) (Fin m) =
      fun r => (pertRhsPInt n m K_B r : K) := by
  funext r
  exact congrArg (Int.cast : ℤ → K) (congrFun (pertRhsQInt_comp_sumComm m n K_B) r)

/-- Boundedness (zero recession cone) of `intMatP B` over any ordered field `K` when `1 ≤ B`. -/
theorem recession_intMatP {m n : ℕ} {B : Matrix (Fin m) (Fin n) ℤ} (hn : 0 < n)
    (hB : ∀ i j, 1 ≤ B i j)
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (v : Fin m → K) (hv : (intMatP B).map Int.cast *ᵥ v ≤ 0) : v = 0 := by
  have hnn : ∀ i, 0 ≤ v i := fun i => by
    simpa [mulVec, dotProduct, intMatP_inl] using hv (.inl i)
  have hBpos (i : Fin m) : (0 : K) < (B i ⟨0, hn⟩ : ℤ) := by
    exact_mod_cast lt_of_lt_of_le Int.zero_lt_one (hB i ⟨0, hn⟩)
  have hsum := Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
    (fun i _ => mul_nonneg (hBpos i).le (hnn i)) |>.1
    (le_antisymm (by simpa [mulVec, dotProduct, intMatP_inr] using hv (.inr ⟨0, hn⟩))
      (Finset.sum_nonneg fun i _ => mul_nonneg (hBpos i).le (hnn i)))
  ext i
  exact (mul_eq_zero.1 (hsum i (Finset.mem_univ i))).resolve_left (hBpos i).ne'

/-- Boundedness (zero recession cone) of `intMatQ A` over any ordered field `K` when `1 ≤ A`. -/
theorem recession_intMatQ {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℤ} (hm : 0 < m)
    (hA : ∀ i j, 1 ≤ A i j)
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (v : Fin n → K) (hv : (intMatQ A).map Int.cast *ᵥ v ≤ 0) : v = 0 :=
  recession_intMatP (B := Aᵀ) hm (fun j i => hA i j) v fun r => by
    rw [← intMatQ_map_submatrix_sumComm A]; exact hv _

/-- `0` is a vertex of `P_ε` with tight rows `Finset.univ.image Sum.inl` when `0 < K_B`. -/
theorem isVertex_zero_pertP {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℤ) {K_B : ℤ} (hK : 0 < K_B)
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    IsVertex ((intMatP B).map Int.cast) (fun r => (pertRhsPInt m n K_B r : K)) 0 ∧
      tightRows ((intMatP B).map Int.cast) (fun r => (pertRhsPInt m n K_B r : K)) (0 : Fin m → K) =
        Finset.univ.image Sum.inl := by
  have hpos (j : Fin n) : (0 : K) < (pertRhsPInt m n K_B (.inr j) : K) := by
    simp only [pertRhsPInt, Sum.elim_inr, Int.cast_add, Int.cast_pow]; positivity
  have htight : tightRows ((intMatP B).map Int.cast)
      (fun r => (pertRhsPInt m n K_B r : K)) (0 : Fin m → K) = Finset.univ.image Sum.inl := by
    ext r; cases r with
    | inl i => simp [mem_tightRows, pertRhsPInt]
    | inr j => simp [mem_tightRows, (hpos j).ne]
  refine ⟨isVertex_iff.2 ⟨fun r => ?_, fun v hv => funext fun i => ?_⟩, htight⟩
  · cases r with
    | inl _ => simp [pertRhsPInt]
    | inr j => simpa using (hpos j).le
  · simpa [intMatP, mulVec, dotProduct, Matrix.one_apply] using
      hv (.inl i) (htight ▸ Finset.mem_image_of_mem _ (Finset.mem_univ i))

/-- `0` is a vertex of `Q_ε` with tight rows `Finset.univ.image Sum.inr` when `0 < K_B`. -/
theorem isVertex_zero_pertQ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) {K_B : ℤ} (hK : 0 < K_B)
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    IsVertex ((intMatQ A).map Int.cast) (fun r => (pertRhsQInt m n K_B r : K)) 0 ∧
      tightRows ((intMatQ A).map Int.cast) (fun r => (pertRhsQInt m n K_B r : K)) (0 : Fin n → K) =
        Finset.univ.image Sum.inr := by
  let e := Equiv.sumComm (Fin n) (Fin m)
  obtain ⟨hv, ht⟩ := isVertex_zero_pertP Aᵀ hK (K := K)
  rw [← intMatQ_map_submatrix_sumComm A (K := K), ← pertRhsQInt_cast_comp_sumComm m n K_B] at hv ht
  rw [tightRows_submatrix_equiv e] at ht
  refine ⟨(isVertex_submatrix_equiv e).1 hv, Finset.ext fun r => ?_⟩
  have h := congrArg (e.symm r ∈ ·) ht
  cases r <;> simpa [e] using h

/-- `(0, 0)` is a completely labelled vertex pair of `(P_ε, Q_ε)`. -/
theorem completelyLabeled_zero_zero_pert {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℤ)
    {K_B : ℤ} (hK : 0 < K_B) {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    LemkeHowson.CompletelyLabeled ((intMatP B).map Int.cast)
      (fun r => (pertRhsPInt m n K_B r : K))
      ((intMatQ A).map Int.cast) (fun r => (pertRhsQInt m n K_B r : K))
      (0 : Fin m → K) (0 : Fin n → K) := by
  rw [LemkeHowson.completelyLabeled_iff]; rintro (i | j) <;>
    simp [(isVertex_zero_pertP B hK (K := K)).2, (isVertex_zero_pertQ A hK (K := K)).2]

end Polytopes

section Nondegeneracy

/-- Every entry of `intMatP B` has absolute value at most `H` when `1 ≤ B i j ≤ H`. -/
theorem abs_intMatP_le {m n H : ℕ} {B : Matrix (Fin m) (Fin n) ℤ} (hH : 1 ≤ H)
    (hB : ∀ i j, 1 ≤ B i j ∧ B i j ≤ H) (r : Fin m ⊕ Fin n) (c : Fin m) :
    |intMatP B r c| ≤ H := by
  cases r with
  | inl i => rw [intMatP_inl]; split_ifs <;> simp [hH]
  | inr j => rw [intMatP_inr, abs_of_pos (by linarith [(hB c j).1])]; exact (hB c j).2

/-- Every entry of `intMatQ A` has absolute value at most `H` when `1 ≤ A i j ≤ H`. -/
theorem abs_intMatQ_le {m n H : ℕ} {A : Matrix (Fin m) (Fin n) ℤ} (hH : 1 ≤ H)
    (hA : ∀ i j, 1 ≤ A i j ∧ A i j ≤ H) (r : Fin m ⊕ Fin n) (c : Fin n) :
    |intMatQ A r c| ≤ H := by
  have h := congrFun (congrFun (intMatQ_submatrix_sumComm A) (Equiv.sumComm (Fin m) (Fin n) r)) c
  simp only [Matrix.submatrix_apply, id_eq, Equiv.sumComm_apply, Sum.swap_swap] at h
  rw [h]
  exact abs_intMatP_le hH (fun j i => hA i j) (Equiv.sumComm (Fin m) (Fin n) r) c

private lemma eq_zero_of_sum_pert_weights {n B : ℕ} {K_B : ℤ}
    (hK : (B : ℤ) * (n + 1) < K_B) {c : Fin n → ℤ} (hbd : ∀ j, |c j| ≤ B)
    (hsum : ∑ j : Fin n, c j * (K_B ^ n + K_B ^ (n - 1 - j.1)) = 0) (j : Fin n) : c j = 0 := by
  have hn : 0 < n := j.pos
  let a : ℕ → ℤ := fun k =>
    if hk : k < n then c ⟨n - 1 - k, by omega⟩
    else if k = n then ∑ j : Fin n, c j else 0
  have hlow : ∑ k ∈ Finset.range n, a k * K_B ^ k = ∑ j : Fin n, c j * K_B ^ (n - 1 - j.1) :=
    Finset.sum_nbij' (fun k => if hk : k < n then ⟨n - 1 - k, by omega⟩ else ⟨0, hn⟩)
      (fun j => n - 1 - j.1) (fun _ _ => Finset.mem_univ _)
      (fun _ _ => Finset.mem_range.2 (by omega))
      (fun k hk => by
        simp only [Finset.mem_range] at hk
        simp only [hk, ↓reduceDIte]; omega)
      (fun j _ => Fin.ext (by
        have hj : n - 1 - j.1 < n := by omega
        simp only [hj, ↓reduceDIte]; omega))
      fun k hk => by
        simp only [Finset.mem_range] at hk
        simp only [a, hk, ↓reduceDIte]
        congr 2
        omega
  have hradix : ∑ k ∈ Finset.range (n + 1), a k * K_B ^ k = 0 := by
    rw [Finset.sum_range_succ, hlow]
    simp only [a, Nat.lt_irrefl, ↓reduceDIte, ↓reduceIte, Finset.sum_mul, ← Finset.sum_add_distrib]
    simpa only [mul_add, add_comm] using hsum
  have ha_bd : ∀ k < n + 1, |a k| < K_B := fun k hk => by
    by_cases hkn : k < n
    · simp only [a, hkn, ↓reduceDIte]; exact (hbd _).trans_lt (by nlinarith)
    · rw [show k = n by omega]
      simp only [a, Nat.lt_irrefl, ↓reduceDIte, ↓reduceIte]
      have hs : |∑ j : Fin n, c j| ≤ (n : ℤ) * B :=
        (Finset.abs_sum_le_sum_abs _ _).trans <|
          (Finset.sum_le_sum fun j _ => hbd j).trans_eq (by simp)
      nlinarith
  have hk0 := Int.eq_zero_of_sum_mul_pow_eq_zero ha_bd hradix (n - 1 - j.1) (by omega)
  simp only [a, show n - 1 - j.1 < n by omega, ↓reduceDIte] at hk0
  rwa [show (⟨n - 1 - (n - 1 - j.1), by omega⟩ : Fin n) = j from Fin.ext (by dsimp; omega)] at hk0

/-- **Nondegeneracy of `P_ε`.** Over any ordered field `K`, if `kernelVecBound m H * (n + 1) < K_B`,
then `intMatP B *ᵥ x ≤ pertRhsPInt m n K_B` is nondegenerate. -/
theorem isNondegenerateSystem_pertP {m n H : ℕ} {B : Matrix (Fin m) (Fin n) ℤ}
    (hH : 1 ≤ H) (hB : ∀ i j, 1 ≤ B i j ∧ B i j ≤ H) {K_B : ℤ}
    (hK : (Matrix.kernelVecBound m H * (n + 1) : ℤ) < K_B)
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    IsNondegenerateSystem ((intMatP B).map Int.cast : Matrix (Fin m ⊕ Fin n) (Fin m) K)
      (fun r => (pertRhsPInt m n K_B r : K)) := by
  rw [isNondegenerateSystem_iff]
  intro x _
  by_contra hlt
  push Not at hlt
  rw [Fintype.card_fin] at hlt
  set T := tightRows ((intMatP B).map Int.cast : Matrix (Fin m ⊕ Fin n) (Fin m) K)
    (fun r => (pertRhsPInt m n K_B r : K)) x
  let M : Matrix (Fin m) T ℤ := fun i r => intMatP B r.1 i
  obtain ⟨c, hc0, hMc, hc_bd⟩ := Matrix.exists_int_mulVec_eq_zero_of_card_lt M
    (fun i r => abs_intMatP_le hH hB r.1 i) (by simp [Fintype.card_coe, hlt])
  rw [Fintype.card_fin] at hc_bd
  have hsumK : ∑ r : T, (c r : K) * (pertRhsPInt m n K_B r.1 : K) = 0 := calc
    ∑ r : T, (c r : K) * (pertRhsPInt m n K_B r.1 : K)
      = ∑ r : T, (c r : K) *
          (((intMatP B).map Int.cast : Matrix (Fin m ⊕ Fin n) (Fin m) K) *ᵥ x) r.1 :=
        Finset.sum_congr rfl fun r _ => by rw [mem_tightRows.1 r.2]
    _ = ∑ i : Fin m, x i * ∑ r : T, (M i r : K) * (c r : K) := by
        simp only [mulVec, dotProduct, Matrix.map_apply, Finset.mul_sum, M]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    _ = 0 := Finset.sum_eq_zero fun i _ => by
        have hi : ∑ r : T, (M i r : K) * (c r : K) = 0 := by
          simpa [mulVec, dotProduct] using congrArg (Int.cast : ℤ → K) (congrFun hMc i)
        rw [hi, mul_zero]
  let cFull : Fin m ⊕ Fin n → ℤ := fun r => if hr : r ∈ T then c ⟨r, hr⟩ else 0
  have hsum_lift (f : Fin m ⊕ Fin n → ℤ) :
      ∑ r : T, c r * f r.1 = ∑ r : Fin m ⊕ Fin n, cFull r * f r := by
    rw [← Finset.sum_subset (Finset.subset_univ T) fun r _ hr => by simp [cFull, hr],
      ← Finset.sum_coe_sort T]
    exact Finset.sum_congr rfl fun r _ => by simp [cFull, r.2]
  have hz : ∑ r : T, c r * pertRhsPInt m n K_B r.1 = 0 :=
    Int.cast_injective (α := K) (by simpa using hsumK)
  rw [hsum_lift, Fintype.sum_sum_type] at hz
  have hc_inr0 : ∀ j : Fin n, cFull (.inr j) = 0 :=
    eq_zero_of_sum_pert_weights (by exact_mod_cast hK)
      (fun j => by by_cases hj : (.inr j : Fin m ⊕ Fin n) ∈ T <;> simp [cFull, hj, hc_bd])
      (by simpa [pertRhsPInt] using hz)
  have hc_inl0 : ∀ i : Fin m, cFull (.inl i) = 0 := fun i => by
    have hi : ∑ r : T, c r * intMatP B r.1 i = 0 := by
      simpa [M, mulVec, dotProduct, mul_comm] using congrFun hMc i
    rw [hsum_lift (fun r => intMatP B r i), Fintype.sum_sum_type] at hi
    simpa [hc_inr0, intMatP_inl] using hi
  exact hc0 <| funext fun ⟨r, hr⟩ => by
    cases r with
    | inl i => simpa [cFull, hr] using hc_inl0 i
    | inr j => simpa [cFull, hr] using hc_inr0 j

/-- **Nondegeneracy of `Q_ε`** derived from `isNondegenerateSystem_pertP` via row transposition. -/
theorem isNondegenerateSystem_pertQ {m n H : ℕ} {A : Matrix (Fin m) (Fin n) ℤ}
    (hH : 1 ≤ H) (hA : ∀ i j, 1 ≤ A i j ∧ A i j ≤ H) {K_B : ℤ}
    (hK : (Matrix.kernelVecBound n H * (m + 1) : ℤ) < K_B)
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    IsNondegenerateSystem ((intMatQ A).map Int.cast : Matrix (Fin m ⊕ Fin n) (Fin n) K)
      (fun r => (pertRhsQInt m n K_B r : K)) := by
  have hnd := isNondegenerateSystem_pertP (B := Aᵀ) hH (fun j i => hA i j) hK (K := K)
  rw [← intMatQ_map_submatrix_sumComm A (K := K), ← pertRhsQInt_cast_comp_sumComm m n K_B] at hnd
  exact (isNondegenerateSystem_submatrix_equiv (Equiv.sumComm (Fin n) (Fin m))).1 hnd

end Nondegeneracy

section BasisVertex

variable {κ : Type*} [Fintype κ] [DecidableEq κ] [LinearOrder κ]

/-- Square integer submatrix indexed by an `m`-element tight basis `T ⊆ κ`. -/
@[expose] def basisMat {k : ℕ} (M_int : Matrix κ (Fin k) ℤ) (T : Finset κ) (hT : T.card = k) :
    Matrix (Fin k) (Fin k) ℤ :=
  M_int.submatrix (fun i => (T.orderIsoOfFin hT i : κ)) id

/-- Cramer numerator vector `M.cramer (b|_T)` in `ℤ^k`. -/
@[expose] def cramerVec {k : ℕ} (M_int : Matrix κ (Fin k) ℤ) (b_int : κ → ℤ)
    (T : Finset κ) (hT : T.card = k) : Fin k → ℤ :=
  (basisMat M_int T hT).cramer (fun i => b_int (T.orderIsoOfFin hT i : κ))

/-- Sign-adjusted integer numerator `det(M).sign • cramerVec`. -/
@[expose] def basisSignNum {k : ℕ} (M_int : Matrix κ (Fin k) ℤ) (b_int : κ → ℤ)
    (T : Finset κ) (hT : T.card = k) : Fin k → ℤ :=
  fun i => (basisMat M_int T hT).det.sign * cramerVec M_int b_int T hT i

/-- Positive (when nonsingular) integer denominator `|det(M)|`. -/
@[expose] def basisAbsDet {k : ℕ} (M_int : Matrix κ (Fin k) ℤ) (T : Finset κ) (hT : T.card = k) :
    ℤ :=
  |(basisMat M_int T hT).det|

/-- Exact rational solution `(det M)⁻¹ • cramerVec` to the basis equations
`(M_int|_T) *ᵥ x = b|_T`. -/
@[expose] noncomputable def ratBasisSol {k : ℕ} (M_int : Matrix κ (Fin k) ℤ) (b_int : κ → ℤ)
    (T : Finset κ) (hT : T.card = k) : Fin k → ℚ :=
  fun i => (cramerVec M_int b_int T hT i : ℚ) / ((basisMat M_int T hT).det : ℚ)

/-- Pure integer feasibility and nonsingularity condition for basis `T` of `(M_int, b_int)`. -/
@[expose] def IsFeasibleBasis {k : ℕ} (M_int : Matrix κ (Fin k) ℤ) (b_int : κ → ℤ)
    (T : Finset κ) (hT : T.card = k) : Prop :=
  let M := basisMat M_int T hT
  M.det ≠ 0 ∧ ∀ r : κ, M.det.sign * ((M_int r) ⬝ᵥ cramerVec M_int b_int T hT) ≤ |M.det| * b_int r

omit [Fintype κ] [DecidableEq κ] in
theorem basisSignNum_div_basisAbsDet {k : ℕ} (M_int : Matrix κ (Fin k) ℤ) (b_int : κ → ℤ)
    (T : Finset κ) (hT : T.card = k) (hdet : (basisMat M_int T hT).det ≠ 0) (i : Fin k) :
    (basisSignNum M_int b_int T hT i : ℚ) / (basisAbsDet M_int T hT : ℚ) =
      ratBasisSol M_int b_int T hT i := by
  set D := (basisMat M_int T hT).det
  have hmul : (D.sign * D : ℤ) = |D| := (Int.sign_mul_self D).trans (Int.natCast_natAbs D)
  have hS : (D.sign : ℚ) ≠ 0 :=
    Int.cast_ne_zero.2 fun h => hdet (abs_eq_zero.1 (by simpa [h] using hmul.symm))
  have hmulQ : (D.sign : ℚ) * (D : ℚ) = (basisAbsDet M_int T hT : ℚ) := by
    simpa only [basisAbsDet, Int.cast_mul] using congrArg (Int.cast : ℤ → ℚ) hmul
  rw [← hmulQ, basisSignNum, Int.cast_mul]
  exact mul_div_mul_left _ _ hS

omit [Fintype κ] [DecidableEq κ] in
private lemma basisAbsDet_mul_ratBasisSol {k : ℕ} {M_int : Matrix κ (Fin k) ℤ} {b_int : κ → ℤ}
    {T : Finset κ} {hT : T.card = k} (hdet : (basisMat M_int T hT).det ≠ 0) (r : κ) :
    (basisAbsDet M_int T hT : ℚ) *
      ((M_int.map Int.cast : Matrix κ (Fin k) ℚ) *ᵥ ratBasisSol M_int b_int T hT) r =
      ((M_int r ⬝ᵥ basisSignNum M_int b_int T hT : ℤ) : ℚ) := by
  have hD_ne : (basisAbsDet M_int T hT : ℚ) ≠ 0 := by exact_mod_cast (abs_pos.2 hdet).ne'
  simp only [mulVec, dotProduct, Matrix.map_apply, Int.cast_sum, Int.cast_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← basisSignNum_div_basisAbsDet M_int b_int T hT hdet j]; field_simp [hD_ne]

omit [Fintype κ] [DecidableEq κ] in
theorem ratBasisSol_tight {k : ℕ} {M_int : Matrix κ (Fin k) ℤ} {b_int : κ → ℤ}
    {T : Finset κ} {hT : T.card = k} (hdet : (basisMat M_int T hT).det ≠ 0)
    {r : κ} (hr : r ∈ T)
    {K : Type*} [Field K] [CharZero K] :
    ((M_int.map Int.cast : Matrix κ (Fin k) K) *ᵥ fun i => (ratBasisSol M_int b_int T hT i : K)) r =
      (b_int r : K) := by
  let M := basisMat M_int T hT
  let i₀ : Fin k := (T.orderIsoOfFin hT).symm ⟨r, hr⟩
  have hi₀ : (T.orderIsoOfFin hT i₀ : κ) = r :=
    congrArg Subtype.val ((T.orderIsoOfFin hT).apply_symm_apply ⟨r, hr⟩)
  have hZ : ∑ j : Fin k, M i₀ j * cramerVec M_int b_int T hT j = M.det * b_int r := by
    have h := congrFun (Matrix.mulVec_cramer M fun i => b_int (T.orderIsoOfFin hT i : κ)) i₀
    dsimp only [Pi.smul_apply, smul_eq_mul] at h; rwa [hi₀] at h
  have hrat : ∑ j : Fin k, (M i₀ j : ℚ) * ratBasisSol M_int b_int T hT j = (b_int r : ℚ) := by
    have hQ : ∑ j : Fin k, (M i₀ j : ℚ) * (cramerVec M_int b_int T hT j : ℚ) =
        (M.det : ℚ) * (b_int r : ℚ) := by
      simpa only [Int.cast_sum, Int.cast_mul] using congrArg (Int.cast : ℤ → ℚ) hZ
    simp only [ratBasisSol, div_eq_inv_mul, mul_left_comm, ← Finset.mul_sum, hQ]
    exact mul_inv_cancel_left₀ (Int.cast_ne_zero.2 hdet) _
  have hK := congrArg (Rat.cast : ℚ → K) hrat
  simpa only [mulVec, dotProduct, Matrix.map_apply, Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast,
    M, basisMat, submatrix_apply, id_eq, hi₀] using hK

omit [Fintype κ] [DecidableEq κ] in
theorem isFeasibleBasis_iff_ratBasisSol_le {k : ℕ} {M_int : Matrix κ (Fin k) ℤ} {b_int : κ → ℤ}
    {T : Finset κ} {hT : T.card = k} (hdet : (basisMat M_int T hT).det ≠ 0) :
    IsFeasibleBasis M_int b_int T hT ↔
      (M_int.map Int.cast : Matrix κ (Fin k) ℚ) *ᵥ ratBasisSol M_int b_int T hT ≤
        fun r => (b_int r : ℚ) := by
  have hD_pos : (0 : ℚ) < (basisAbsDet M_int T hT : ℚ) := Int.cast_pos.2 (abs_pos.2 hdet)
  have hr_iff (r : κ) :
      (basisMat M_int T hT).det.sign * (M_int r ⬝ᵥ cramerVec M_int b_int T hT) ≤
        |(basisMat M_int T hT).det| * b_int r ↔
      ((M_int.map Int.cast : Matrix κ (Fin k) ℚ) *ᵥ ratBasisSol M_int b_int T hT) r ≤ b_int r := by
    rw [show (basisMat M_int T hT).det.sign * (M_int r ⬝ᵥ cramerVec M_int b_int T hT) =
        M_int r ⬝ᵥ basisSignNum M_int b_int T hT by
          simp only [dotProduct, basisSignNum, Finset.mul_sum, mul_left_comm],
      ← Int.cast_le (R := ℚ), Int.cast_mul]
    change ((M_int r ⬝ᵥ basisSignNum M_int b_int T hT : ℤ) : ℚ) ≤
      (basisAbsDet M_int T hT : ℚ) * (b_int r : ℚ) ↔ _
    rw [← basisAbsDet_mul_ratBasisSol hdet r, mul_le_mul_iff_right₀ hD_pos]
  exact ⟨fun hfb r => (hr_iff r).1 (hfb.2 r), fun h => ⟨hdet, fun r => (hr_iff r).2 (h r)⟩⟩

omit [DecidableEq κ] in
theorem isVertex_ratBasisSol_of_isFeasibleBasis {k : ℕ} {M_int : Matrix κ (Fin k) ℤ}
    {b_int : κ → ℤ} {T : Finset κ} {hT : T.card = k}
    (hfb : IsFeasibleBasis M_int b_int T hT)
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    IsVertex (M_int.map Int.cast : Matrix κ (Fin k) K) (fun r => (b_int r : K))
        (fun i => (ratBasisSol M_int b_int T hT i : K)) ∧
      T ⊆ tightRows (M_int.map Int.cast : Matrix κ (Fin k) K) (fun r => (b_int r : K))
        (fun i => (ratBasisSol M_int b_int T hT i : K)) := by
  have hleK : (M_int.map Int.cast : Matrix κ (Fin k) K) *ᵥ
      (fun i => (ratBasisSol M_int b_int T hT i : K)) ≤ fun r => (b_int r : K) := fun r => by
    simpa only [mulVec, dotProduct, Matrix.map_apply, Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast]
      using (Rat.cast_le (K := K)).2 ((isFeasibleBasis_iff_ratBasisSol_le hfb.1).1 hfb r)
  have hsub : T ⊆ tightRows (M_int.map Int.cast : Matrix κ (Fin k) K) (fun r => (b_int r : K))
      (fun i => (ratBasisSol M_int b_int T hT i : K)) :=
    fun _ hr => mem_tightRows.2 (ratBasisSol_tight hfb.1 hr)
  have hdetK : ((M_int.map Int.cast : Matrix κ (Fin k) K).submatrix
      (fun i => ((T.orderIsoOfFin hT).toEquiv i : κ)) id).det ≠ 0 := by
    change ((basisMat M_int T hT).map (Int.cast : ℤ → K)).det ≠ 0
    rw [← Int.cast_det]; exact Int.cast_ne_zero.2 hfb.1
  exact ⟨isVertex_of_det_submatrix_ne_zero hleK hsub (T.orderIsoOfFin hT).toEquiv hdetK, hsub⟩

omit [DecidableEq κ] in
theorem tightRows_ratBasisSol_eq {k : ℕ} {M_int : Matrix κ (Fin k) ℤ} {b_int : κ → ℤ}
    {T : Finset κ} {hT : T.card = k} (hfb : IsFeasibleBasis M_int b_int T hT)
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (hnd : IsNondegenerateSystem (M_int.map Int.cast : Matrix κ (Fin k) K)
      (fun r => (b_int r : K))) :
    tightRows (M_int.map Int.cast : Matrix κ (Fin k) K) (fun r => (b_int r : K))
      (fun i => (ratBasisSol M_int b_int T hT i : K)) = T := by
  obtain ⟨hvx, hsub⟩ := isVertex_ratBasisSol_of_isFeasibleBasis hfb (K := K)
  exact (Finset.eq_of_subset_of_card_le hsub
    (by simpa only [Fintype.card_fin, hT] using (hvx.card_tightRows hnd).le)).symm

omit [DecidableEq κ] in
theorem exists_isFeasibleBasis_of_isVertex {k : ℕ} {M_int : Matrix κ (Fin k) ℤ} {b_int : κ → ℤ}
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (hnd : IsNondegenerateSystem (M_int.map Int.cast : Matrix κ (Fin k) K)
      (fun r => (b_int r : K)))
    {x : Fin k → K} (hx : IsVertex (M_int.map Int.cast : Matrix κ (Fin k) K)
      (fun r => (b_int r : K)) x) :
    let T := tightRows (M_int.map Int.cast : Matrix κ (Fin k) K) (fun r => (b_int r : K)) x
    ∃ hT : T.card = k,
      IsFeasibleBasis M_int b_int T hT ∧
        x = fun i => (ratBasisSol M_int b_int T hT i : K) := by
  intro T
  have hT : T.card = k := by simpa only [Fintype.card_fin] using hx.card_tightRows hnd
  have hdetK := hx.det_submatrix_ne_zero (T.orderIsoOfFin hT).toEquiv
  have hdetZ : (basisMat M_int T hT).det ≠ 0 := by
    have : ((basisMat M_int T hT).map (Int.cast : ℤ → K)).det ≠ 0 := hdetK
    rw [← Int.cast_det] at this; exact fun h => this (by simp [h])
  have hxeq : x = fun i => (ratBasisSol M_int b_int T hT i : K) :=
    Matrix.mulVec_injective_of_det_ne_zero hdetK <| funext fun i => by
      change ((M_int.map Int.cast : Matrix κ (Fin k) K) *ᵥ x) (T.orderIsoOfFin hT i : κ) =
        ((M_int.map Int.cast : Matrix κ (Fin k) K) *ᵥ _) (T.orderIsoOfFin hT i : κ)
      rw [mem_tightRows.1 (T.orderIsoOfFin hT i).2,
        ratBasisSol_tight hdetZ (T.orderIsoOfFin hT i).2]
  have hleQ : (M_int.map Int.cast : Matrix κ (Fin k) ℚ) *ᵥ ratBasisSol M_int b_int T hT ≤
      fun r => (b_int r : ℚ) := fun r => by
    rw [← Rat.cast_le (K := K)]
    have hrx := hx.mulVec_le r
    rw [hxeq] at hrx
    simpa only [mulVec, dotProduct, Matrix.map_apply, Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast]
      using hrx
  exact ⟨hT, (isFeasibleBasis_iff_ratBasisSol_le hdetZ).2 hleQ, hxeq⟩

omit [Fintype κ] [DecidableEq κ] in
theorem abs_det_basisMat_le {k H : ℕ} {M_int : Matrix κ (Fin k) ℤ}
    (hM : ∀ r c, |M_int r c| ≤ H) (T : Finset κ) (hT : T.card = k) :
    |(basisMat M_int T hT).det| ≤ (k.factorial * H ^ k : ℕ) := by
  have hmat : ∀ r c, |basisMat M_int T hT r c| ≤ (H : ℤ) := fun i j => hM _ j
  simpa [nsmul_eq_mul] using Matrix.det_le (abv := AbsoluteValue.abs) hmat

omit [Fintype κ] [DecidableEq κ] in
theorem abs_cramerVec_le {k H : ℕ} {M_int : Matrix κ (Fin k) ℤ} {b_int : κ → ℤ}
    (hM : ∀ r c, |M_int r c| ≤ H) (hb : ∀ r, |b_int r| ≤ H) (T : Finset κ) (hT : T.card = k)
    (i : Fin k) :
    |cramerVec M_int b_int T hT i| ≤ (k.factorial * H ^ k : ℕ) := by
  simpa only [cramerVec, Fintype.card_fin] using Matrix.abs_cramer_le (A := basisMat M_int T hT)
    (b := fun j => b_int (T.orderIsoOfFin hT j : κ)) (fun r c => hM _ c) (fun r => hb _) i

omit [Fintype κ] [DecidableEq κ] in
private theorem abs_basisSignNum_le {k H : ℕ} {M_int : Matrix κ (Fin k) ℤ} {b_int : κ → ℤ}
    (hM : ∀ r c, |M_int r c| ≤ H) (hb : ∀ r, |b_int r| ≤ H)
    (T : Finset κ) (hT : T.card = k) (i : Fin k) :
    |basisSignNum M_int b_int T hT i| ≤ (k.factorial * H ^ k : ℕ) := by
  have hsign : |(basisMat M_int T hT).det.sign| ≤ 1 := by
    rcases lt_trichotomy (basisMat M_int T hT).det 0 with h | h | h <;>
      simp [Int.sign_eq_neg_one_of_neg, Int.sign_eq_one_of_pos, h]
  rw [basisSignNum, abs_mul]
  exact (mul_le_mul hsign (abs_cramerVec_le hM hb T hT i) (abs_nonneg _) zero_le_one).trans_eq
    (one_mul _)

/-- Cramer perturbation bound: if `M : Matrix (Fin k) (Fin k) ℤ` is nonsingular with `|M r c| ≤ H`
and `|(M *ᵥ d) i| ≤ K_B⁻¹`, then `|d j| ≤ k! * H^k / K_B`. -/
private lemma cramer_pert_le {k H : ℕ} {M : Matrix (Fin k) (Fin k) ℤ} {K_B : ℤ} {d : Fin k → ℚ}
    (hH : 1 ≤ H) (hK : 0 < K_B) (hdet : M.det ≠ 0) (hM : ∀ r c, |M r c| ≤ H)
    (hres : ∀ i, |((M.map Int.cast : Matrix (Fin k) (Fin k) ℚ) *ᵥ d) i| ≤ (K_B : ℚ)⁻¹)
    (j : Fin k) :
    |d j| ≤ ((k.factorial * H ^ k : ℕ) : ℚ) / (K_B : ℚ) := by
  set MQ : Matrix (Fin k) (Fin k) ℚ := M.map Int.cast
  have hK_posQ : (0 : ℚ) < K_B := by exact_mod_cast hK
  have hdetQ_eq : MQ.det = (M.det : ℚ) := (Int.cast_det M).symm
  have hdetQ : MQ.det ≠ 0 := by rw [hdetQ_eq]; exact_mod_cast hdet
  have hMc : (M.det : ℚ) • d = MQ.cramer (MQ *ᵥ d) :=
    Matrix.mulVec_injective_of_det_ne_zero hdetQ <| by
      rw [Matrix.mulVec_cramer, mulVec_smul, hdetQ_eq]
  have hcol : ∀ r c, |(MQ.updateCol j ((K_B : ℚ) • (MQ *ᵥ d))) r c| ≤ (H : ℚ) := fun r c => by
    by_cases hc : c = j
    · subst hc
      simp only [Matrix.updateCol_self, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hK_posQ]
      exact ((mul_le_mul_of_nonneg_left (hres r) hK_posQ.le).trans_eq
        (mul_inv_cancel₀ hK_posQ.ne')).trans (by exact_mod_cast hH)
    · simp only [Matrix.updateCol_ne hc, MQ, Matrix.map_apply]; exact_mod_cast hM r c
  have hdet_bd : |(K_B : ℚ) * (M.det : ℚ) * d j| ≤ ((k.factorial * H ^ k : ℕ) : ℚ) := by
    rw [mul_assoc, show (M.det : ℚ) * d j = (MQ.updateCol j (MQ *ᵥ d)).det by
          simpa only [Pi.smul_apply, smul_eq_mul, Matrix.cramer_apply] using congrFun hMc j,
      ← Matrix.det_updateCol_smul]
    simpa [nsmul_eq_mul] using Matrix.det_le (abv := AbsoluteValue.abs) hcol
  have hD1 : (1 : ℚ) ≤ |(M.det : ℚ)| := by exact_mod_cast Int.one_le_abs hdet
  rw [abs_mul, abs_mul, abs_of_pos hK_posQ] at hdet_bd
  rw [le_div_iff₀ hK_posQ, mul_comm]
  calc (K_B : ℚ) * |d j| = (K_B : ℚ) * 1 * |d j| := by ring
    _ ≤ (K_B : ℚ) * |(M.det : ℚ)| * |d j| := by gcongr
    _ ≤ _ := hdet_bd

omit [Fintype κ] [DecidableEq κ] in
/-- Core Cramer rounding theorem: if the perturbed rhs `b_pert` satisfies
`0 ≤ b_pert - K_B^p * b_unpert ≤ K_B^(p-1)` (`p ≥ 1`) with
`K_B > (k! * H^k) * (1 + k * k! * H^(k+1))`,
then any feasible basis `T` for `(M_int, b_pert)` gives an **exact** feasible solution
`basisSignNum M_int b_unpert T hT` for the unperturbed integer system `(M_int, b_unpert)` with
all rows in `T` still tight. -/
theorem unperturbed_feasible_of_pert {k H p : ℕ} {M_int : Matrix κ (Fin k) ℤ}
    {b_pert b_unpert : κ → ℤ} {T : Finset κ} {hT : T.card = k} {K_B : ℤ}
    (hk : 0 < k) (hH : 1 ≤ H) (hp : 1 ≤ p)
    (hM : ∀ r c, |M_int r c| ≤ H)
    (hb_pert_diff : ∀ r, 0 ≤ b_pert r - K_B ^ p * b_unpert r ∧
      b_pert r - K_B ^ p * b_unpert r ≤ K_B ^ (p - 1))
    (hK : ((k.factorial * H ^ k) * (1 + k * k.factorial * H ^ (k + 1)) : ℤ) < K_B)
    (hfb : IsFeasibleBasis M_int b_pert T hT) :
    (basisMat M_int T hT).det ≠ 0 ∧
      (∀ r ∈ T, M_int r ⬝ᵥ basisSignNum M_int b_unpert T hT =
        basisAbsDet M_int T hT * b_unpert r) ∧
      (∀ r : κ, M_int r ⬝ᵥ basisSignNum M_int b_unpert T hT ≤
        basisAbsDet M_int T hT * b_unpert r) := by
  have hdet := hfb.1
  have hK_pos : 0 < K_B :=
    lt_of_le_of_lt (by positivity : (0 : ℤ) ≤ _) hK
  have hK_posQ : (0 : ℚ) < K_B := by exact_mod_cast hK_pos
  have hKp_pos : (0 : ℚ) < (K_B : ℚ) ^ p := pow_pos hK_posQ p
  have hpert_div_le (r : κ) :
      (b_pert r : ℚ) / (K_B : ℚ) ^ p ≤ (b_unpert r : ℚ) + (K_B : ℚ)⁻¹ := by
    have hbd : (b_pert r : ℚ) ≤ (K_B : ℚ) ^ p * b_unpert r + (K_B : ℚ) ^ (p - 1) := by
      linarith [show (b_pert r : ℚ) - (K_B : ℚ) ^ p * b_unpert r ≤ (K_B : ℚ) ^ (p - 1) from
        by exact_mod_cast (hb_pert_diff r).2]
    refine (div_le_div_of_nonneg_right hbd hKp_pos.le).trans_eq ?_
    rw [show (K_B : ℚ) ^ p = (K_B : ℚ) * (K_B : ℚ) ^ (p - 1) by
          rw [← pow_succ', Nat.sub_add_cancel hp]]
    field_simp [hK_posQ.ne']
  set M := basisMat M_int T hT
  set u : Fin k → ℚ := ((K_B : ℚ) ^ p)⁻¹ • ratBasisSol M_int b_pert T hT
  set v : Fin k → ℚ := ratBasisSol M_int b_unpert T hT
  have hu_le (r : κ) : ((M_int.map Int.cast : Matrix κ (Fin k) ℚ) *ᵥ u) r ≤
      (b_unpert r : ℚ) + (K_B : ℚ)⁻¹ := by
    rw [mulVec_smul, Pi.smul_apply, smul_eq_mul, inv_mul_eq_div]
    exact (div_le_div_of_nonneg_right ((isFeasibleBasis_iff_ratBasisSol_le hdet).1 hfb r)
      hKp_pos.le).trans (hpert_div_le r)
  have hres (i : Fin k) :
      |((M.map Int.cast : Matrix (Fin k) (Fin k) ℚ) *ᵥ (u - v)) i| ≤ (K_B : ℚ)⁻¹ := by
    let ri : κ := (T.orderIsoOfFin hT i : κ)
    have hri : ri ∈ T := (T.orderIsoOfFin hT i).2
    have hδ : ((M.map Int.cast : Matrix (Fin k) (Fin k) ℚ) *ᵥ (u - v)) i =
        (b_pert ri : ℚ) / (K_B : ℚ) ^ p - b_unpert ri := by
      rw [mulVec_sub, Pi.sub_apply]
      change ((M_int.map Int.cast : Matrix κ (Fin k) ℚ) *ᵥ u) ri -
        ((M_int.map Int.cast : Matrix κ (Fin k) ℚ) *ᵥ v) ri = _
      rw [mulVec_smul, Pi.smul_apply, smul_eq_mul, inv_mul_eq_div]
      simpa only [Rat.cast_id] using congr_arg₂ (fun a b => a / (K_B : ℚ) ^ p - b)
        (ratBasisSol_tight hdet hri (K := ℚ)) (ratBasisSol_tight hdet hri (K := ℚ))
    have hlo : (0 : ℚ) ≤ (b_pert ri : ℚ) - (K_B : ℚ) ^ p * b_unpert ri := by
      exact_mod_cast (hb_pert_diff ri).1
    rw [hδ, abs_of_nonneg (sub_nonneg.2 <| (le_div_iff₀ hKp_pos).2 (by linarith)),
      sub_le_iff_le_add']
    exact hpert_div_le ri
  have hdiff_bd := cramer_pert_le hH hK_pos hdet (fun _ c => hM _ c) hres
  refine ⟨hdet, fun r hr => Int.cast_injective (α := ℚ) ?_, fun r => ?_⟩
  · rw [Int.cast_mul, ← basisAbsDet_mul_ratBasisSol (b_int := b_unpert) hdet r]
    simpa only [Rat.cast_id] using congrArg ((basisAbsDet M_int T hT : ℚ) * ·)
      (ratBasisSol_tight (b_int := b_unpert) hdet hr (K := ℚ))
  · have hrow_diff : |((M_int.map Int.cast : Matrix κ (Fin k) ℚ) *ᵥ v) r -
        ((M_int.map Int.cast : Matrix κ (Fin k) ℚ) *ᵥ u) r| ≤
        (k : ℚ) * H * (((k.factorial * H ^ k : ℕ) : ℚ) / K_B) := by
      rw [← Pi.sub_apply, ← mulVec_sub, mulVec, dotProduct]
      refine (Finset.abs_sum_le_sum_abs _ _).trans <|
        (Finset.sum_le_sum (g := fun _ => (H : ℚ) * (((k.factorial * H ^ k : ℕ) : ℚ) / K_B))
          fun j _ => ?_).trans_eq (by simp [mul_assoc])
      rw [abs_mul, Pi.sub_apply, Matrix.map_apply, abs_sub_comm]
      exact mul_le_mul (by exact_mod_cast hM r j) (hdiff_bd j) (abs_nonneg _) (Nat.cast_nonneg _)
    have hv_le : ((M_int.map Int.cast : Matrix κ (Fin k) ℚ) *ᵥ v) r - b_unpert r ≤
        ((1 + k * k.factorial * H ^ (k + 1) : ℕ) : ℚ) / K_B := by
      have hrhs : (K_B : ℚ)⁻¹ + (k : ℚ) * H * (((k.factorial * H ^ k : ℕ) : ℚ) / K_B) =
          ((1 + k * k.factorial * H ^ (k + 1) : ℕ) : ℚ) / K_B := by
        push_cast; rw [pow_succ']; field_simp [hK_posQ.ne']
      linarith [(abs_sub_le_iff.1 hrow_diff).1, hu_le r]
    have hD_le : (basisAbsDet M_int T hT : ℚ) ≤ ((k.factorial * H ^ k : ℕ) : ℚ) := by
      exact_mod_cast abs_det_basisMat_le hM T hT
    have hD_pos : (0 : ℚ) < basisAbsDet M_int T hT := by exact_mod_cast abs_pos.2 hdet
    have hlt : ((M_int r ⬝ᵥ basisSignNum M_int b_unpert T hT -
        basisAbsDet M_int T hT * b_unpert r : ℤ) : ℚ) < 1 := by
      rw [Int.cast_sub, Int.cast_mul, ← basisAbsDet_mul_ratBasisSol hdet r, ← mul_sub]
      calc (basisAbsDet M_int T hT : ℚ) * (_ - _)
          ≤ (basisAbsDet M_int T hT : ℚ) * _ := mul_le_mul_of_nonneg_left hv_le hD_pos.le
        _ ≤ ((k.factorial * H ^ k : ℕ) : ℚ) * _ := by gcongr
        _ < 1 := by rw [mul_div_assoc', div_lt_one hK_posQ]; exact_mod_cast hK
    have hZ : M_int r ⬝ᵥ basisSignNum M_int b_unpert T hT -
        basisAbsDet M_int T hT * b_unpert r < 1 := by exact_mod_cast hlt
    omega

end BasisVertex

section ExactRecovery

private lemma pertRhsPInt_diff (m n : ℕ) {K_B : ℤ} (hK : 0 < K_B) (r : Fin m ⊕ Fin n) :
    0 ≤ pertRhsPInt m n K_B r - K_B ^ n * intRhsP m n r ∧
      pertRhsPInt m n K_B r - K_B ^ n * intRhsP m n r ≤ K_B ^ (n - 1) := by
  cases r with
  | inl i =>
    simp only [pertRhsPInt, intRhsP, Sum.elim_inl, Pi.zero_apply, mul_zero, sub_zero]
    exact ⟨le_rfl, pow_nonneg hK.le _⟩
  | inr j =>
    simp only [pertRhsPInt, intRhsP, Sum.elim_inr, Pi.one_apply, mul_one, add_sub_cancel_left]
    exact ⟨pow_nonneg hK.le _, pow_le_pow_right₀ (by omega) (Nat.sub_le (n - 1) j.1)⟩

private lemma finset_eq_image_of_forall_mem {α β : Type*} [Fintype β] [DecidableEq α]
    {S : Finset α} {f : β → α} (hf : Function.Injective f) (hcard : S.card = Fintype.card β)
    (hsub : ∀ x ∈ S, ∃ y, f y = x) : S = Finset.univ.image f :=
  Finset.eq_of_subset_of_card_le
    (fun x hx => let ⟨y, hy⟩ := hsub x hx; hy ▸ Finset.mem_image_of_mem _ (Finset.mem_univ y))
    (by rw [Finset.card_image_of_injective _ hf, Finset.card_univ, hcard])

private lemma sum_pos_of_nonneg_of_dot_pos {ι : Type*} [Fintype ι] {v w : ι → ℤ} {D : ℤ}
    (hD : 0 < D) (hw : ∀ i, 0 ≤ w i) (hdot : v ⬝ᵥ w = D) :
    w ≠ 0 ∧ 0 < ∑ i : ι, w i := by
  have hne : w ≠ 0 := fun h0 => by rw [h0, dotProduct_zero] at hdot; omega
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hne
  have hpos : 0 < w i₀ := lt_of_le_of_ne (hw i₀) hi₀.symm
  have hle : w i₀ ≤ ∑ i : ι, w i :=
    Finset.single_le_sum (fun i _ => hw i) (Finset.mem_univ i₀)
  exact ⟨hne, by omega⟩

private lemma intMat_map_mulVec_div {κ : Type*} {k : ℕ} (M_int : Matrix κ (Fin k) ℤ)
    (num : Fin k → ℤ) (D : ℤ) (r : κ) :
    ((M_int.map (Int.cast : ℤ → ℝ)) *ᵥ (fun i => (num i : ℝ) / (D : ℝ))) r =
      ((M_int r ⬝ᵥ num : ℤ) : ℝ) / (D : ℝ) := by
  simp only [mulVec, dotProduct, Matrix.map_apply, Int.cast_sum, Int.cast_mul,
    div_eq_mul_inv, ← mul_assoc, ← Finset.sum_mul]

private lemma inv_sum_smul_div {ι : Type*} [Fintype ι] (num : ι → ℤ) {D : ℤ}
    (hD : (0 : ℝ) < D) (hS : (0 : ℝ) < (∑ i : ι, num i : ℤ)) :
    (∑ i : ι, (num i : ℝ) / (D : ℝ))⁻¹ • (fun i => (num i : ℝ) / (D : ℝ)) =
      fun i => (num i : ℝ) / ((∑ i : ι, num i : ℤ) : ℝ) := by
  ext i
  have hsum : ∑ i : ι, (num i : ℝ) / (D : ℝ) = ((∑ i : ι, num i : ℤ) : ℝ) / (D : ℝ) := by
    simp only [div_eq_mul_inv, ← Finset.sum_mul, Int.cast_sum]
  simp only [Pi.smul_apply, smul_eq_mul, hsum, inv_div]
  field_simp [hD.ne', hS.ne']

private lemma exists_mixed_of_partition {m n : ℕ} {T₁ T₂ : Finset (Fin m ⊕ Fin n)}
    (hT₁ : T₁.card = m) (hT₂ : T₂.card = n) (huniv : T₁ ∪ T₂ = Finset.univ)
    (hne0 : (T₁, T₂) ≠ (Finset.univ.image Sum.inl, Finset.univ.image Sum.inr)) :
    (∃ j : Fin n, Sum.inr j ∈ T₁) ∧ (∃ i : Fin m, Sum.inl i ∈ T₂) := by
  have hdisj : Disjoint T₁ T₂ := Finset.disjoint_iff_inter_eq_empty.2 <|
    Finset.card_eq_zero.1 <| by
      have huc := Finset.card_union_add_card_inter T₁ T₂
      rw [hT₁, hT₂, huniv, Finset.card_univ, Fintype.card_sum, Fintype.card_fin,
        Fintype.card_fin] at huc
      omega
  have hT₁_ne : T₁ ≠ Finset.univ.image Sum.inl := fun h1 => hne0 (Prod.ext h1 <|
    finset_eq_image_of_forall_mem Sum.inr_injective (by simpa using hT₂) fun
      | .inl i, hr => absurd hr (Finset.disjoint_left.1 hdisj (h1 ▸ by simp))
      | .inr j, _ => ⟨j, rfl⟩)
  have hex_inr : ∃ j : Fin n, Sum.inr j ∈ T₁ := by
    by_contra h; push Not at h
    exact hT₁_ne <| finset_eq_image_of_forall_mem Sum.inl_injective (by simpa using hT₁) fun
      | .inl i, _ => ⟨i, rfl⟩
      | .inr j, hr => absurd hr (h j)
  refine ⟨hex_inr, by
    by_contra h; push Not at h
    have h2 : T₂ = Finset.univ.image Sum.inr := finset_eq_image_of_forall_mem
      Sum.inr_injective (by simpa using hT₂) fun
        | .inl i, hr => absurd hr (h i)
        | .inr j, _ => ⟨j, rfl⟩
    obtain ⟨j, hj⟩ := hex_inr
    exact Finset.disjoint_left.1 hdisj hj (h2 ▸ by simp)⟩

/-- Exact Nash equilibrium extraction from any nonzero completely labelled basis pair `(T₁, T₂)`
of `(P_ε, Q_ε)` with `K_B = 2 ^ bitBound m n H`. -/
theorem isNash_extractNum {m n H : ℕ} [LinearOrder (Fin m ⊕ Fin n)]
    {A B : Matrix (Fin m) (Fin n) ℤ}
    (hm : 0 < m) (hn : 0 < n) (hH : 1 ≤ H)
    (hA : ∀ i j, 1 ≤ A i j ∧ A i j ≤ H) (hB : ∀ i j, 1 ≤ B i j ∧ B i j ≤ H)
    {T₁ T₂ : Finset (Fin m ⊕ Fin n)} {hT₁ : T₁.card = m} {hT₂ : T₂.card = n}
    (hP : IsFeasibleBasis (intMatP B) (pertRhsPInt m n ((2 : ℤ) ^ bitBound m n H)) T₁ hT₁)
    (hQ : IsFeasibleBasis (intMatQ A) (pertRhsQInt m n ((2 : ℤ) ^ bitBound m n H)) T₂ hT₂)
    (huniv : T₁ ∪ T₂ = Finset.univ)
    (hne0 : (T₁, T₂) ≠ (Finset.univ.image Sum.inl, Finset.univ.image Sum.inr)) :
    let numP := basisSignNum (intMatP B) (intRhsP m n) T₁ hT₁
    let numQ := basisSignNum (intMatQ A) (intRhsQ m n) T₂ hT₂
    let S₁ := ∑ i : Fin m, numP i
    let S₂ := ∑ j : Fin n, numQ j
    (∀ i, 0 ≤ numP i) ∧ 0 < S₁ ∧ (∀ i, |numP i| ≤ (m.factorial * H ^ m : ℕ)) ∧
      (∀ j, 0 ≤ numQ j) ∧ 0 < S₂ ∧ (∀ j, |numQ j| ≤ (n.factorial * H ^ n : ℕ)) ∧
      ({ A := A.map Int.cast, B := B.map Int.cast } : BimatrixGame (Fin m) (Fin n)).IsNash
        (fun i => (numP i : ℝ) / (S₁ : ℝ)) (fun j => (numQ j : ℝ) / (S₂ : ℝ)) := by
  intro numP numQ S₁ S₂
  let K_B : ℤ := (2 : ℤ) ^ bitBound m n H
  have hK_pos : 0 < K_B := by positivity
  obtain ⟨hdetP, hP_tight, hP_le⟩ := unperturbed_feasible_of_pert hm hH hn
    (abs_intMatP_le hH hB) (pertRhsPInt_diff m n hK_pos)
    (by dsimp only [K_B]; exact_mod_cast cramerScale_lt_two_pow_bitBound (H := H) hm hn) hP
  obtain ⟨hdetQ, hQ_tight, hQ_le⟩ := unperturbed_feasible_of_pert hn hH hm
    (abs_intMatQ_le hH hA) (fun r => by
      simpa only [← pertRhsQInt_comp_sumComm m n K_B, ← intRhsQ_comp_sumComm m n,
        Function.comp_apply, Equiv.sumComm_apply, Sum.swap_swap] using
        pertRhsPInt_diff n m hK_pos (Equiv.sumComm (Fin m) (Fin n) r))
    (by dsimp only [K_B]; exact_mod_cast cramerScale_lt_two_pow_bitBound_symm (H := H) hm hn) hQ
  set D₁ := basisAbsDet (intMatP B) T₁ hT₁
  set D₂ := basisAbsDet (intMatQ A) T₂ hT₂
  have hD₁ : 0 < D₁ := abs_pos.2 hdetP
  have hD₂ : 0 < D₂ := abs_pos.2 hdetQ
  have hnumP_nn (i : Fin m) : 0 ≤ numP i := by
    simpa [numP, intRhsP, dotProduct, intMatP_inl] using hP_le (.inl i)
  have hnumQ_nn (j : Fin n) : 0 ≤ numQ j := by
    simpa [numQ, intRhsQ, dotProduct, intMatQ_inr] using hQ_le (.inr j)
  obtain ⟨⟨j₀, hj₀⟩, ⟨i₀, hi₀⟩⟩ := exists_mixed_of_partition hT₁ hT₂ huniv hne0
  obtain ⟨hnumP_ne, hS₁⟩ := sum_pos_of_nonneg_of_dot_pos hD₁ hnumP_nn
    ((hP_tight (.inr j₀) hj₀).trans (by simp [intRhsP]))
  obtain ⟨_, hS₂⟩ := sum_pos_of_nonneg_of_dot_pos hD₂ hnumQ_nn
    ((hQ_tight (.inl i₀) hi₀).trans (by simp [intRhsQ]))
  refine ⟨hnumP_nn, hS₁,
    abs_basisSignNum_le (abs_intMatP_le hH hB) (fun r => by cases r <;> simp [intRhsP, hH]) T₁ hT₁,
    hnumQ_nn, hS₂,
    abs_basisSignNum_le (abs_intMatQ_le hH hA) (fun r => by cases r <;> simp [intRhsQ, hH]) T₂ hT₂,
    ?_⟩
  let G : BimatrixGame (Fin m) (Fin n) := ⟨A.map Int.cast, B.map Int.cast⟩
  let x₀ : Fin m → ℝ := fun i => (numP i : ℝ) / D₁
  let y₀ : Fin n → ℝ := fun j => (numQ j : ℝ) / D₂
  have hD₁R : (0 : ℝ) < D₁ := by exact_mod_cast hD₁
  have hD₂R : (0 : ℝ) < D₂ := by exact_mod_cast hD₂
  have hrhsP (r) : rhsP (Fin m) (Fin n) r = (intRhsP m n r : ℝ) := by
    cases r <;> simp [rhsP_inl, rhsP_inr, intRhsP]
  have hrhsQ (r) : rhsQ (Fin m) (Fin n) r = (intRhsQ m n r : ℝ) := by
    cases r <;> simp [rhsQ_inl, rhsQ_inr, intRhsQ]
  have hx₀_le : G.matP *ᵥ x₀ ≤ rhsP (Fin m) (Fin n) := fun r => by
    rw [← intMatP_map_eq_matP A B, intMat_map_mulVec_div, hrhsP, div_le_iff₀ hD₁R, mul_comm]
    exact_mod_cast hP_le r
  have hy₀_le : G.matQ *ᵥ y₀ ≤ rhsQ (Fin m) (Fin n) := fun r => by
    rw [← intMatQ_map_eq_matQ A B, intMat_map_mulVec_div, hrhsQ, div_le_iff₀ hD₂R, mul_comm]
    exact_mod_cast hQ_le r
  have hcl : LemkeHowson.CompletelyLabeled G.matP (rhsP (Fin m) (Fin n))
      G.matQ (rhsQ (Fin m) (Fin n)) x₀ y₀ :=
    LemkeHowson.completelyLabeled_iff.2 fun r => by
      rcases Finset.mem_union.1 (huniv ▸ Finset.mem_univ r) with hr1 | hr2
      · left; rw [mem_tightRows, ← intMatP_map_eq_matP A B, intMat_map_mulVec_div, hrhsP,
          div_eq_iff hD₁R.ne', mul_comm]; exact_mod_cast hP_tight r hr1
      · right; rw [mem_tightRows, ← intMatQ_map_eq_matQ A B, intMat_map_mulVec_div, hrhsQ,
          div_eq_iff hD₂R.ne', mul_comm]; exact_mod_cast hQ_tight r hr2
  have hx₀_ne : x₀ ≠ 0 := fun h0 => hnumP_ne <| funext fun i => by
    simpa [x₀, hD₁.ne'] using congrFun h0 i
  change G.IsNash _ _
  simpa only [x₀, y₀, inv_sum_smul_div numP hD₁R (by exact_mod_cast hS₁),
    inv_sum_smul_div numQ hD₂R (by exact_mod_cast hS₂)] using
    isNash_of_completelyLabeled hx₀_le hy₀_le hcl hx₀_ne

end ExactRecovery

section RationalNormalization

/-- Common denominator scaling factor for two rational `m × n` payoff matrices. -/
@[expose] def clearDenomScale {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℚ) : ℕ :=
  ∏ i : Fin m, ∏ j : Fin n, (A i j).den * (B i j).den

theorem clearDenomScale_pos {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℚ) :
    0 < clearDenomScale A B := by
  refine Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => ?_
  exact Nat.mul_pos (Nat.pos_of_ne_zero (A i j).den_nz) (Nat.pos_of_ne_zero (B i j).den_nz)

private lemma dvd_clearDenomScale_of_dvd_mul {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℚ)
    (i : Fin m) (j : Fin n) {d : ℕ} (hd : d ∣ (A i j).den * (B i j).den) :
    d ∣ clearDenomScale A B :=
  dvd_trans hd (dvd_trans
    (Finset.dvd_prod_of_mem (fun c => (A i c).den * (B i c).den) (Finset.mem_univ j))
    (Finset.dvd_prod_of_mem (fun r => ∏ c : Fin n, (A r c).den * (B r c).den)
      (Finset.mem_univ i)))

theorem den_dvd_clearDenomScale_left {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℚ)
    (i : Fin m) (j : Fin n) : (A i j).den ∣ clearDenomScale A B :=
  dvd_clearDenomScale_of_dvd_mul A B i j (dvd_mul_right _ _)

theorem den_dvd_clearDenomScale_right {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℚ)
    (i : Fin m) (j : Fin n) : (B i j).den ∣ clearDenomScale A B :=
  dvd_clearDenomScale_of_dvd_mul A B i j (dvd_mul_left _ _)

/-- Integer numerator after scaling `M` by `clearDenomScale A B`. -/
@[expose] def clearDenomInt {m n : ℕ} (A B M : Matrix (Fin m) (Fin n) ℚ) :
    Matrix (Fin m) (Fin n) ℤ :=
  fun i j => (M i j).num * ((clearDenomScale A B / (M i j).den : ℕ) : ℤ)

/-- Shift constant guaranteeing positivity of both scaled payoff matrices. -/
@[expose] def clearDenomShift {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℚ) : ℤ :=
  1 + ∑ i : Fin m, ∑ j : Fin n,
    (|clearDenomInt A B A i j| + |clearDenomInt A B B i j|)

/-- Positive integer normalized first payoff matrix. -/
@[expose] def clearDenomPosA {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℚ) :
    Matrix (Fin m) (Fin n) ℤ :=
  fun i j => clearDenomInt A B A i j + clearDenomShift A B

/-- Positive integer normalized second payoff matrix. -/
@[expose] def clearDenomPosB {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℚ) :
    Matrix (Fin m) (Fin n) ℤ :=
  fun i j => clearDenomInt A B B i j + clearDenomShift A B

/-- Entry upper bound `H` for both `clearDenomPosA A B` and `clearDenomPosB A B`. -/
@[expose] def clearDenomBound {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℚ) : ℕ :=
  2 * (clearDenomShift A B).natAbs

private lemma one_le_clearDenomShift {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℚ) :
    1 ≤ clearDenomShift A B :=
  le_add_of_nonneg_right <| Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _)

theorem one_le_clearDenomBound {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℚ) :
    1 ≤ clearDenomBound A B := by
  have := one_le_clearDenomShift A B; unfold clearDenomBound; omega

theorem clearDenomPos_bounds {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℚ) (i : Fin m) (j : Fin n) :
    1 ≤ clearDenomPosA A B i j ∧ clearDenomPosA A B i j ≤ clearDenomBound A B ∧
      1 ≤ clearDenomPosB A B i j ∧ clearDenomPosB A B i j ≤ clearDenomBound A B := by
  have hS := one_le_clearDenomShift A B
  have hterm : |clearDenomInt A B A i j| + |clearDenomInt A B B i j| ≤ clearDenomShift A B - 1 := by
    have h1 := Finset.single_le_sum (s := Finset.univ)
      (f := fun c => |clearDenomInt A B A i c| + |clearDenomInt A B B i c|)
      (fun _ _ => by positivity) (Finset.mem_univ j)
    have h2 := Finset.single_le_sum (s := Finset.univ)
      (f := fun r => ∑ c : Fin n, (|clearDenomInt A B A r c| + |clearDenomInt A B B r c|))
      (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i)
    dsimp only [clearDenomShift]; linarith
  have hA := abs_le.1 (show |clearDenomInt A B A i j| ≤ clearDenomShift A B - 1 by
    linarith [abs_nonneg (clearDenomInt A B B i j)])
  have hB := abs_le.1 (show |clearDenomInt A B B i j| ≤ clearDenomShift A B - 1 by
    linarith [abs_nonneg (clearDenomInt A B A i j)])
  have hpos : ((clearDenomShift A B).natAbs : ℤ) = clearDenomShift A B :=
    Int.natAbs_of_nonneg (by omega)
  dsimp only [clearDenomPosA, clearDenomPosB, clearDenomBound]; omega

/-- Nash equilibria of the positive integer normalized game `⟨clearDenomPosA, clearDenomPosB⟩`
coincide with Nash equilibria of the rational game `⟨A, B⟩`. -/
theorem isNash_clearDenomPos {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℚ)
    (x : Fin m → ℝ) (y : Fin n → ℝ) :
    (BimatrixGame.mk ((clearDenomPosA A B).map Int.cast)
        ((clearDenomPosB A B).map Int.cast) : BimatrixGame (Fin m) (Fin n)).IsNash x y ↔
      (BimatrixGame.mk (A.map Rat.cast) (B.map Rat.cast) :
        BimatrixGame (Fin m) (Fin n)).IsNash x y := by
  let D : ℝ := ((clearDenomScale A B : ℕ) : ℝ)
  have hD : 0 < D := by dsimp only [D]; exact_mod_cast clearDenomScale_pos A B
  have hcast (M : Matrix (Fin m) (Fin n) ℚ)
      (hd : ∀ i j, (M i j).den ∣ clearDenomScale A B) (i j) :
      ((clearDenomInt A B M i j : ℤ) : ℝ) = D * (M i j : ℝ) := by
    have hden_ne : ((M i j).den : ℝ) ≠ 0 := by exact_mod_cast (M i j).den_nz
    have hnat : ((M i j).den : ℝ) * ((clearDenomScale A B / (M i j).den : ℕ) : ℝ) = D := by
      dsimp only [D]; exact_mod_cast Nat.mul_div_cancel' (hd i j)
    have hrat : ((M i j : ℚ) : ℝ) = ((M i j).num : ℝ) / ((M i j).den : ℝ) := by
      exact_mod_cast (Rat.num_div_den (M i j)).symm
    simp only [clearDenomInt, Int.cast_mul, Int.cast_natCast]
    rw [hrat, ← hnat]; field_simp
  let G : BimatrixGame (Fin m) (Fin n) := ⟨A.map Rat.cast, B.map Rat.cast⟩
  let GD : BimatrixGame (Fin m) (Fin n) := ⟨D • G.A, D • G.B⟩
  have hadd : (⟨(clearDenomPosA A B).map Int.cast,
      (clearDenomPosB A B).map Int.cast⟩ : BimatrixGame (Fin m) (Fin n)) =
      GD.addConst (clearDenomShift A B : ℝ) := congr_arg₂ BimatrixGame.mk
    (by ext i j; simp [GD, G, clearDenomPosA, hcast A (den_dvd_clearDenomScale_left A B)])
    (by ext i j; simp [GD, G, clearDenomPosB, hcast B (den_dvd_clearDenomScale_right A B)])
  rw [hadd, isNash_addConst, isNash_smul hD G]

end RationalNormalization

end Cslib.GameTheory.BimatrixGame
