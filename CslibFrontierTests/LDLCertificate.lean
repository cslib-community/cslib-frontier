/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Algorithms.LinearAlgebra.LDLCertificate
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for `Cslib.LinearAlgebra.LDLCert`

Every acceptance and rejection below is closed by `decide +kernel`, so the kernel evaluates the
checker. The cases are those of #8319: the positive-definite example `P`, a singular positive
semidefinite matrix, corrupted factors, an indefinite and a nonsymmetric matrix, mismatched
certificate dimensions, the empty dimension, a residual `N - M ⪰ 0`, the Lyapunov client for
`A = !![0, 1; -2, -3]`, and a dense `8 × 8` regression case.
-/

public section

namespace Cslib.LinearAlgebra.LDLCertificateTests

open Matrix Mathlib.Tactic.Matrix Cslib.LinearAlgebra

/-! ### The positive-definite example of #8319 -/

/-- The rows of `P = !![5/4, 1/4; 1/4, 1/4] = L * diagonal d * Lᵀ`, with `L = !![1, 0; 1/5, 1]`
and `d = (5/4, 1/5)`. -/
def P : List (List ℚ) := [[5/4, 1/4], [1/4, 1/4]]

def certP : LDLCert := ⟨[[1], [1/5, 1]], [5/4, 1/5]⟩

theorem certP_ok : certP.checkPosDef 2 P = true := by decide +kernel

/-- `ofLists` is the `!![…]` matrix. -/
example : ofLists 2 2 P = !![5/4, 1/4; 1/4, 1/4] := rfl

/-- The caller's form: Mathlib's `PosDef` of the real matrix. -/
theorem P_posDef : (!![5/4, 1/4; 1/4, 1/4] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
  convert certP.posDef_of_checkPosDef certP_ok using 1
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [P]

/-- The factor `L` that the certificate denotes. -/
example : certP.L 2 = !![1, 0; 1/5, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- A corrupted off-diagonal entry of `L`. -/
example : (⟨[[1], [1/4, 1]], [5/4, 1/5]⟩ : LDLCert).checkPosDef 2 P = false := by decide +kernel

/-- A corrupted entry of `d`. -/
example : (⟨[[1], [1/5, 1]], [5/4, 1/4]⟩ : LDLCert).checkPosDef 2 P = false := by decide +kernel

/-- A non-unit diagonal entry of `L`, with `d` adjusted so that the product is still `P`. -/
example : (⟨[[1], [1/5, 2]], [5/4, 1/20]⟩ : LDLCert).checkPosDef 2 P = false := by
  decide +kernel

/-- An entry above the diagonal of `L`, even a zero one. -/
example : (⟨[[1, 0], [1/5, 1]], [5/4, 1/5]⟩ : LDLCert).checkPosDef 2 P = false := by
  decide +kernel

/-! ### A singular positive semidefinite matrix -/

def J : List (List ℚ) := [[1, 1], [1, 1]]

def certJ : LDLCert := ⟨[[1], [1, 1]], [1, 0]⟩

theorem certJ_ok : certJ.checkPosSemidef 2 J = true := by decide +kernel

example : ((ofLists 2 2 J).map ((↑) : ℚ → ℝ)).PosSemidef :=
  certJ.posSemidef_of_checkPosSemidef certJ_ok

/-- The zero pivot is rejected as a definiteness witness. -/
example : certJ.checkPosDef 2 J = false := by decide +kernel

/-! ### An indefinite matrix -/

def K : List (List ℚ) := [[1, 2], [2, 1]]

/-- The exact factorization `K = L * diagonal (1, -3) * Lᵀ` is accepted as a factorization, but
its negative pivot is rejected. -/
example : (⟨[[1], [2, 1]], [1, -3]⟩ : LDLCert).factors 2 K = true := by decide +kernel

example : (⟨[[1], [2, 1]], [1, -3]⟩ : LDLCert).checkPosSemidef 2 K = false := by decide +kernel

/-- `K` is indefinite, so soundness rules out every certificate. -/
theorem K_rejected (c : LDLCert) : c.checkPosSemidef 2 K = false := by
  by_contra h
  have hK := (c.posSemidef_of_checkPosSemidef
    (Bool.eq_true_of_not_eq_false h)).dotProduct_mulVec_nonneg ![1, -1]
  norm_num [K, ofLists_apply, ofList_apply, dotProduct, mulVec, Fin.sum_univ_two] at hK

/-! ### A nonsymmetric matrix -/

def N₀ : List (List ℚ) := [[1, 1], [0, 1]]

/-- The certificate read off the lower triangle of `N₀` is rejected. -/
example : (⟨[[1], [0, 1]], [1, 1]⟩ : LDLCert).factors 2 N₀ = false := by decide +kernel

/-- An accepted factorization is symmetric, so every certificate is rejected. -/
theorem N₀_rejected (c : LDLCert) : c.factors 2 N₀ = false := by
  by_contra h
  have hM := c.eq_of_factors (Bool.eq_true_of_not_eq_false h)
  have hT : (ofLists 2 2 N₀)ᵀ = ofLists 2 2 N₀ := by
    rw [hM, transpose_mul, transpose_mul, transpose_transpose, diagonal_transpose,
      Matrix.mul_assoc]
  have h01 := congrFun (congrFun hT 0) 1
  norm_num [N₀, ofLists_apply, ofList_apply] at h01

/-! ### Malformed input, mismatched dimensions and the empty dimension -/

/-- A certificate for `3 × 3` matrices is rejected on a `2 × 2` one. -/
example : (⟨[[1], [1/5, 1], [0, 0, 1]], [5/4, 1/5, 1]⟩ : LDLCert).checkPosDef 2 P = false := by
  decide +kernel

/-- A diagonal of the wrong length is rejected. -/
example : (⟨[[1], [1/5, 1]], [5/4, 1/5, 1]⟩ : LDLCert).checkPosDef 2 P = false := by
  decide +kernel

/-- Rows of `P` checked as a `3 × 3` matrix, a ragged matrix, and a padded `P` are all rejected,
although `ofLists` would read the missing entries as zeros. -/
example : certP.checkPosDef 3 P = false := by decide +kernel

example : certP.checkPosDef 2 [[5/4, 1/4], [1/4]] = false := by decide +kernel

example : certP.checkPosDef 2 [[5/4, 1/4], [1/4, 1/4], []] = false := by decide +kernel

/-- The empty `0 × 0` matrix has the empty certificate, and it is positive definite: there is no
nonzero vector. -/
theorem empty_ok : (⟨[], []⟩ : LDLCert).checkPosDef 0 [] = true := by decide +kernel

example : ((ofLists 0 0 ([] : List (List ℚ))).map ((↑) : ℚ → ℝ)).PosDef :=
  LDLCert.posDef_of_checkPosDef _ empty_ok

/-- A nonempty certificate, or a nonempty row list, is rejected in dimension `0`. -/
example : (⟨[[1]], [1]⟩ : LDLCert).checkPosDef 0 [] = false := by decide +kernel

example : (⟨[], []⟩ : LDLCert).checkPosDef 0 [[]] = false := by decide +kernel

/-! ### Matrix operations and residuals -/

/-- Transpose, product and entrywise operations on rows agree with Mathlib's matrices; the
kernel evaluates the left-hand sides. -/
example : rowsMul 2 2 2 (ListMatrix.transpose 2 P) P = [[13/8, 3/8], [3/8, 1/8]] := by
  decide +kernel

/-- `N - 1 = J` for `N = !![2, 1; 1, 2]` is singular positive semidefinite, so `1 ⪯ N`. The
residual `N - 1` is recomputed from `N` and `1` by `rowsMap₂`. -/
def N : List (List ℚ) := [[2, 1], [1, 2]]

def I₂ : List (List ℚ) := [[1, 0], [0, 1]]

theorem residual_ok : certJ.checkPosSemidef 2 (rowsMap₂ (· - ·) 2 2 N I₂) = true := by
  decide +kernel

example : ((ofLists 2 2 N).map ((↑) : ℚ → ℝ) - (ofLists 2 2 I₂).map ((↑) : ℚ → ℝ)).PosSemidef := by
  have h := certJ.posSemidef_of_checkPosSemidef residual_ok
  rw [ofLists_rowsMap₂] at h
  convert h using 1
  ext i j
  simp

/-! ### The Lyapunov client -/

def A : List (List ℚ) := [[0, 1], [-2, -3]]

/-- `-(Aᵀ * P + P * A) = 1`, checked by the kernel on lists of rows. -/
theorem lyapunov_identity :
    -((ofLists 2 2 A)ᵀ * ofLists 2 2 P + ofLists 2 2 P * ofLists 2 2 A) = 1 := by
  rw [← ofLists_lyapunovResidual, show lyapunovResidual 2 A P = I₂ by decide +kernel]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- `P ≻ 0`, and the recomputed residual `-(Aᵀ * P + P * A) = 1` has the certificate `L = 1`,
`d = (1, 1)`. -/
def certA : LyapunovCert := ⟨certP, ⟨[[1], [0, 1]], [1, 1]⟩⟩

theorem certA_ok : certA.check 2 A P = true := by decide +kernel

example : ((ofLists 2 2 P).map ((↑) : ℚ → ℝ)).PosDef ∧
    (-(((ofLists 2 2 A).map ((↑) : ℚ → ℝ))ᵀ * (ofLists 2 2 P).map ((↑) : ℚ → ℝ) +
      (ofLists 2 2 P).map ((↑) : ℚ → ℝ) * (ofLists 2 2 A).map ((↑) : ℚ → ℝ))).PosDef :=
  LyapunovCert.posDef_of_check certA_ok

/-- For the unstable `A = 1` the residual is `-2 P`, and the same certificate is rejected. -/
example : certA.check 2 I₂ P = false := by decide +kernel

/-- A malformed `A` is rejected. -/
example : certA.check 2 [[0, 1], [-2]] P = false := by decide +kernel

/-! ### Regression benchmark

A dense `8 × 8` instance generated by an untrusted SymPy script: `M₈ = B Bᵀ + 1` for a random
rational `B` with 8-bit numerators and a common denominator, and SymPy's `LDLdecomposition`
as the witness (130-bit entries). Kernel replay takes about 0.1 s; a run above 1 s is a
regression of the checker. -/

def M₈ : List (List ℚ) :=
  [[142063/15129, -33773/5043, 29482/15129, 54136/15129, -52730/15129, 36458/5043, -48821/15129,
    43504/15129],
    [-33773/5043, 87262/5043, 34061/15129, 8779/15129, 33373/15129, -127970/15129, -23111/15129,
      17857/5043],
    [29482/15129, 34061/15129, 60194/5043, 89699/15129, 51811/15129, -50743/15129, -73159/15129,
      99692/15129],
    [54136/15129, 8779/15129, 89699/15129, 32668/5043, 12914/15129, -22411/15129, -7532/1681,
      41839/15129],
    [-52730/15129, 33373/15129, 51811/15129, 12914/15129, 166976/15129, -125848/15129, 27850/15129,
      36445/15129],
    [36458/5043, -127970/15129, -50743/15129, -22411/15129, -125848/15129, 26415/1681, 1451/1681,
      23573/15129],
    [-48821/15129, -23111/15129, -73159/15129, -7532/1681, 27850/15129, 1451/1681, 45514/5043,
      -74902/15129],
    [43504/15129, 17857/5043, 99692/15129, 41839/15129, 36445/15129, 23573/15129, -74902/15129,
      215314/15129]]

def c₈ : LDLCert := ⟨[[1],
    [-101319/142063, 1],
    [29482/142063, 7825894601/26924564757, 1],
    [54136/142063, 6732176461/26924564757, 1741757950463668/4266249460293011, 1],
    [-52730/142063, -601482371/26924564757, 1722756483234784/4266249460293011,
      33890489356874288549/166872808760686381659, 1],
    [109374/142063, -7098137804/26924564757, -1586351806763795/4266249460293011,
      -117504495504662834425/166872808760686381659,
      -9508728654450734428862753/20001119998920132242268832, 1],
    [-48821/142063, -8229712892/26924564757, -1243628169929321/4266249460293011,
      -22528016541646235860/55624269586895460553,
      1264222243237239659167725/5000279999730033060567208,
      429042867132149666817071940188/1439354808682958428515567997773, 1],
    [43504/142063, 4006079583/8974854919, 1779026477050929/4266249460293011,
      -97559247046000076104/166872808760686381659,
      2707100275898456601328655/10000559999460066121134416,
      31543703448746559891233199958/62580643855780801239807304251,
      -62049751805330919234529602215021863/98050908542884923354179356054465112, 1]],
    [142063/15129, 8974854919/716423709, 4266249460293011/407341740208653,
      55624269586895460553/21514696028257654473, 487832195095612981518752/61576066432693274832171,
      479784936227652809505189332591/100865648154554226897761719776,
      98050908542884923354179356054465112/21775998900564478065012028238307717,
      751293841120394824391920617951639859027/164823577260589556158375497527555853272]⟩

theorem c₈_ok : c₈.checkPosDef 8 M₈ = true := by decide +kernel

end Cslib.LinearAlgebra.LDLCertificateTests
