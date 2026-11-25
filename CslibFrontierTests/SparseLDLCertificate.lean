/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Algorithms.LinearAlgebra.SparseLDLCertificate
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for `Cslib.LinearAlgebra.EnvLDLCert` and `Cslib.LinearAlgebra.SparseLyapunovCert`

Every acceptance and rejection below is closed by `decide +kernel`, so the kernel evaluates the
checker. The cases mirror those of the dense checker's tests: the positive-definite example
`P = !![5/4, 1/4; 1/4, 1/4]` in sparse form, exactly and with a diagonally dominant remainder,
corrupted certificates, an envelope that misses a nonzero entry, unsorted columns, a remainder
that is not diagonally dominant, a nonsymmetric matrix, the empty dimension, the Lyapunov client
for `A = !![0, 1; -2, -3]`, and generated regression certificates for RLC ladders and an RC tree.
-/

public section

namespace Cslib.LinearAlgebra.SparseLDLCertificateTests

open Matrix Mathlib.Tactic.Matrix Cslib.LinearAlgebra

/-! ### The format -/

/-- The dense rows of `P`. -/
def Pd : List (List ℚ) := [[5/4, 1/4], [1/4, 1/4]]

/-- The sparse rows of `P`. -/
def P : List (List (ℕ × ℚ)) := [[(0, 5/4), (1, 1/4)], [(0, 1/4), (1, 1/4)]]

/-- The sparse form of the dense rows is `P`, and it reads as the same matrix as `ofLists`. -/
example : Pd.map (toSparseFrom 0) = P := by decide +kernel

example : ofSparse 2 2 P = ofLists 2 2 Pd := by
  rw [show P = Pd.map (toSparseFrom 0) by decide +kernel, ofSparse_toSparse]

/-- Repeated columns add up, and a missing row is zero. -/
example : sparseGet [(1, (1 : ℚ)), (0, 2), (1, 3)] 1 = 4 := by decide +kernel

example : (ofSparse 2 2 ([[(0, 1)]] : List (List (ℕ × ℚ)))) 1 1 = 0 := by decide +kernel

/-! ### Exact and remainder certificates for `P` -/

/-- The exact envelope certificate `L = !![1, 0; 1/5, 1]`, `d = (5/4, 1/5)`. -/
def certP : EnvLDLCert := ⟨[(0, [1]), (0, [1/5, 1])], [5/4, 1/5], []⟩

theorem certP_ok : certP.checkPosDef 2 P = true := by decide +kernel

/-- The caller's form: Mathlib's `PosDef` of the real matrix, as for the dense checker. -/
example : ((ofLists 2 2 Pd).map ((↑) : ℚ → ℝ)).PosDef := by
  rw [← ofSparse_toSparse, show Pd.map (toSparseFrom 0) = P by decide +kernel]
  exact certP.posDef_of_checkPosDef certP_ok

/-- An exact certificate factors `P`, and its factor is that of the dense certificate. -/
example : ofSparse 2 2 P = certP.toLDLCert.L 2 * diagonal (certP.toLDLCert.d 2) *
    (certP.toLDLCert.L 2)ᵀ :=
  certP.eq_of_factors (by decide +kernel) rfl

example : certP.toLDLCert.lower = [[1], [1/5, 1]] := by decide +kernel

/-- A rounded certificate: `L = !![1, 0; 1/4, 1]` and `d = (1, 1/10)` leave the diagonal
remainder `P - L * diagonal d * Lᵀ = diagonal (1/4, 7/80)`. -/
def certPr : EnvLDLCert :=
  ⟨[(0, [1]), (0, [1/4, 1])], [1, 1/10], [[(0, 1/4)], [(1, 7/80)]]⟩

theorem certPr_ok : certPr.checkPosDef 2 P = true := by decide +kernel

/-- A corrupted entry of `L`, of `d`, or of the remainder. -/
example : (⟨[(0, [1]), (0, [1/4, 1])], [5/4, 1/5], []⟩ : EnvLDLCert).checkPosDef 2 P = false := by
  decide +kernel

example : (⟨[(0, [1]), (0, [1/5, 1])], [5/4, 1/4], []⟩ : EnvLDLCert).checkPosDef 2 P = false := by
  decide +kernel

example : (⟨[(0, [1]), (0, [1/4, 1])], [1, 1/10], [[(0, 1/4)], [(1, 1/80)]]⟩ :
    EnvLDLCert).checkPosDef 2 P = false := by decide +kernel

/-- A non-unit diagonal entry of `L`. -/
example : (⟨[(0, [1]), (0, [1/5, 2])], [5/4, 1/20], []⟩ : EnvLDLCert).checkPosDef 2 P = false := by
  decide +kernel

/-- An envelope that starts row `1` at column `1` misses the nonzero entry `P 1 0`. -/
example : (⟨[(0, [1]), (1, [1])], [5/4, 1/4], []⟩ : EnvLDLCert).checkPosDef 2 P = false := by
  decide +kernel

/-- Columns out of order are rejected, though they read as the same matrix. -/
example : certP.checkPosDef 2 [[(1, 1/4), (0, 5/4)], [(0, 1/4), (1, 1/4)]] = false := by
  decide +kernel

/-! ### A singular matrix and an indefinite one -/

/-- `J = !![1, 1; 1, 1]` is singular positive semidefinite. -/
def J : List (List (ℕ × ℚ)) := [[(0, 1), (1, 1)], [(0, 1), (1, 1)]]

def certJ : EnvLDLCert := ⟨[(0, [1]), (0, [1, 1])], [1, 0], []⟩

theorem certJ_ok : certJ.checkPosSemidef 2 J = true := by decide +kernel

example : ((ofSparse 2 2 J).map ((↑) : ℚ → ℝ)).PosSemidef :=
  certJ.posSemidef_of_checkPosSemidef certJ_ok

example : certJ.checkPosDef 2 J = false := by decide +kernel

/-- `K = !![1, 2; 2, 1]` is indefinite: `K - R = 1` for the remainder `R = !![0, 2; 2, 0]`, but
`R` is not diagonally dominant and is rejected. -/
def K : List (List (ℕ × ℚ)) := [[(0, 1), (1, 2)], [(0, 2), (1, 1)]]

example : (⟨[(0, [1]), (1, [1])], [1, 1], [[(1, 2)], [(0, 2)]]⟩ : EnvLDLCert).checkPosDef 2 K =
    false := by decide +kernel

/-- Soundness rules out every certificate for `K`. -/
theorem K_rejected (c : EnvLDLCert) : c.checkPosSemidef 2 K = false := by
  by_contra h
  have hK := (c.posSemidef_of_checkPosSemidef
    (Bool.eq_true_of_not_eq_false h)).dotProduct_mulVec_nonneg ![1, -1]
  norm_num [K, ofSparse_apply, sparseGet_cons, dotProduct, mulVec, Fin.sum_univ_two] at hK

/-- A nonsymmetric matrix is rejected. -/
example : (⟨[(0, [1]), (0, [0, 1])], [1, 1], []⟩ : EnvLDLCert).checkPosDef 2
    [[(0, 1), (1, 1)], [(1, 1)]] = false := by decide +kernel

/-! ### Mismatched dimensions and the empty dimension -/

example : certP.checkPosDef 3 P = false := by decide +kernel

example : (⟨[(0, [1]), (0, [1/5, 1])], [5/4, 1/5, 1], []⟩ : EnvLDLCert).checkPosDef 2 P =
    false := by decide +kernel

theorem empty_ok : (⟨[], [], []⟩ : EnvLDLCert).checkPosDef 0 [] = true := by decide +kernel

example : ((ofSparse 0 0 ([] : List (List (ℕ × ℚ)))).map ((↑) : ℚ → ℝ)).PosDef :=
  EnvLDLCert.posDef_of_checkPosDef _ empty_ok

/-! ### Products, transposes and the Lyapunov client -/

def A : List (List (ℕ × ℚ)) := [[(1, 1)], [(0, -2), (1, -3)]]

def At : List (List (ℕ × ℚ)) := [[(1, -2)], [(0, 1), (1, -3)]]

example : isTransposeOf A At = true := by decide +kernel

example : isTransposeOf A A = false := by decide +kernel

/-- The residual `-(Aᵀ * P + P * A) = 1`, recomputed on sparse rows. -/
example : sparseResidual A At P = [[(0, 1), (1, 0)], [(0, 0), (1, 1)]] := by decide +kernel

def certA : SparseLyapunovCert := ⟨At, certP, ⟨[(0, [1]), (1, [1])], [1, 1], []⟩⟩

theorem certA_ok : certA.check 2 A P = true := by decide +kernel

/-- The statement has the shape of the dense `LyapunovCert.posDef_of_check`. -/
example : ((ofSparse 2 2 P).map ((↑) : ℚ → ℝ)).PosDef ∧
    (-(((ofSparse 2 2 A).map ((↑) : ℚ → ℝ))ᵀ * (ofSparse 2 2 P).map ((↑) : ℚ → ℝ) +
      (ofSparse 2 2 P).map ((↑) : ℚ → ℝ) * (ofSparse 2 2 A).map ((↑) : ℚ → ℝ))).PosDef :=
  SparseLyapunovCert.posDef_of_check certA_ok

/-- A wrong transpose, and the unstable `A = 1`, are rejected. -/
example : (⟨A, certP, ⟨[(0, [1]), (1, [1])], [1, 1], []⟩⟩ : SparseLyapunovCert).check 2 A P =
    false := by decide +kernel

example : certA.check 2 [[(0, 1)], [(1, 1)]] P = false := by decide +kernel

/-! ### Regression benchmarks

Three instances generated by the untrusted script of the module documentation (SciPy and
Clarabel for a banded `P`, a rounded envelope `LDLᵀ` and its exact diagonally dominant remainder),
in the sparse certificate layout: every rational written `mkRat (.ofNat p) q` or
`mkRat (.negSucc p) q`, so that elaboration is linear.

* An 8-state RLC ladder with unit components and a tridiagonal `P`; kernel replay takes about
  0.3 s, the budget is 1 s.
* The 32-state ladder; about 1.5 s, the budget is 4 s.
* An RC network on a 15-node binary tree, numbered in post-order, with `P = 1`; about 0.3 s, the
  budget is 1 s.

A run above its budget is a regression of the checker. -/

def lad8_A : List (List (ℕ × ℚ)) :=
  [[(0, mkRat (.negSucc 0) 1), (1, mkRat (.negSucc 0) 1)],
    [(0, mkRat (.ofNat 1) 1), (2, mkRat (.negSucc 0) 1)],
    [(1, mkRat (.ofNat 1) 1), (3, mkRat (.negSucc 0) 1)],
    [(2, mkRat (.ofNat 1) 1), (4, mkRat (.negSucc 0) 1)],
    [(3, mkRat (.ofNat 1) 1), (5, mkRat (.negSucc 0) 1)],
    [(4, mkRat (.ofNat 1) 1), (6, mkRat (.negSucc 0) 1)],
    [(5, mkRat (.ofNat 1) 1), (7, mkRat (.negSucc 0) 1)],
    [(6, mkRat (.ofNat 1) 1), (7, mkRat (.negSucc 0) 1)]]

def lad8_P : List (List (ℕ × ℚ)) :=
  [[(0, mkRat (.ofNat 43) 4), (1, mkRat (.ofNat 23) 4)],
    [(0, mkRat (.ofNat 23) 4), (1, mkRat (.ofNat 243) 16), (2, mkRat (.ofNat 7) 2)],
    [(1, mkRat (.ofNat 7) 2), (2, mkRat (.ofNat 237) 16), (3, mkRat (.ofNat 27) 16)],
    [(2, mkRat (.ofNat 27) 16), (3, mkRat (.ofNat 59) 4)],
    [(4, mkRat (.ofNat 59) 4), (5, mkRat (.negSucc 26) 16)],
    [(4, mkRat (.negSucc 26) 16), (5, mkRat (.ofNat 237) 16), (6, mkRat (.negSucc 6) 2)],
    [(5, mkRat (.negSucc 6) 2), (6, mkRat (.ofNat 243) 16), (7, mkRat (.negSucc 22) 4)],
    [(6, mkRat (.negSucc 22) 4), (7, mkRat (.ofNat 43) 4)]]

def lad8_At : List (List (ℕ × ℚ)) :=
  [[(0, mkRat (.negSucc 0) 1), (1, mkRat (.ofNat 1) 1)],
    [(0, mkRat (.negSucc 0) 1), (2, mkRat (.ofNat 1) 1)],
    [(1, mkRat (.negSucc 0) 1), (3, mkRat (.ofNat 1) 1)],
    [(2, mkRat (.negSucc 0) 1), (4, mkRat (.ofNat 1) 1)],
    [(3, mkRat (.negSucc 0) 1), (5, mkRat (.ofNat 1) 1)],
    [(4, mkRat (.negSucc 0) 1), (6, mkRat (.ofNat 1) 1)],
    [(5, mkRat (.negSucc 0) 1), (7, mkRat (.ofNat 1) 1)],
    [(6, mkRat (.negSucc 0) 1), (7, mkRat (.negSucc 0) 1)]]

def lad8_plower : List (ℕ × List ℚ) :=
  [(0, [mkRat (.ofNat 1) 1]),
    (0, [mkRat (.ofNat 97) 128, mkRat (.ofNat 1) 1]),
    (1, [mkRat (.ofNat 29) 64, mkRat (.ofNat 1) 1]),
    (2, [mkRat (.ofNat 43) 256, mkRat (.ofNat 1) 1]),
    (4, [mkRat (.ofNat 1) 1]),
    (4, [mkRat (.negSucc 36) 256, mkRat (.ofNat 1) 1]),
    (5, [mkRat (.negSucc 38) 128, mkRat (.ofNat 1) 1]),
    (6, [mkRat (.negSucc 66) 128, mkRat (.ofNat 1) 1])]

def lad8_pdiag : List ℚ :=
  [mkRat (.ofNat 1947) 256, mkRat (.ofNat 1971) 256, mkRat (.ofNat 645) 64,
      mkRat (.ofNat 2899) 256, mkRat (.ofNat 2971) 256, mkRat (.ofNat 2925) 256,
      mkRat (.ofNat 2809) 256, mkRat (.ofNat 147) 32]

def lad8_prem : List (List (ℕ × ℚ)) :=
  [[(0, mkRat (.ofNat 805) 256), (1, mkRat (.negSucc 442) 32768)],
    [(0, mkRat (.negSucc 442) 32768), (1, mkRat (.ofNat 13088805) 4194304), (2,
      mkRat (.ofNat 185) 16384)],
    [(1, mkRat (.ofNat 185) 16384), (2, mkRat (.ofNat 3306741) 1048576), (3,
      mkRat (.negSucc 86) 16384)],
    [(2, mkRat (.negSucc 86) 16384), (3, mkRat (.ofNat 13176163) 4194304)],
    [(4, mkRat (.ofNat 805) 256), (5, mkRat (.negSucc 664) 65536)],
    [(4, mkRat (.negSucc 664) 65536), (5, mkRat (.ofNat 52752413) 16777216), (6,
      mkRat (.negSucc 612) 32768)],
    [(5, mkRat (.negSucc 612) 32768), (6, mkRat (.ofNat 13229411) 4194304), (7,
      mkRat (.negSucc 212) 32768)],
    [(6, mkRat (.negSucc 212) 32768), (7, mkRat (.ofNat 13211583) 4194304)]]

def lad8_qlower : List (ℕ × List ℚ) :=
  [(0, [mkRat (.ofNat 1) 1]),
    (0, [mkRat (.ofNat 35) 256, mkRat (.ofNat 1) 1]),
    (0, [mkRat (.ofNat 61) 256, mkRat (.ofNat 1) 64, mkRat (.ofNat 1) 1]),
    (1, [mkRat (.ofNat 61) 128, mkRat (.ofNat 3) 256, mkRat (.ofNat 1) 1]),
    (2, [mkRat (.ofNat 167) 256, mkRat (.negSucc 2) 256, mkRat (.ofNat 1) 1]),
    (3, [mkRat (.ofNat 107) 128, mkRat (.negSucc 2) 128, mkRat (.ofNat 1) 1]),
    (4, [mkRat (.ofNat 261) 256, mkRat (.negSucc 48) 256, mkRat (.ofNat 1) 1]),
    (5, [mkRat (.ofNat 337) 256, mkRat (.negSucc 26) 64, mkRat (.ofNat 1) 1])]

def lad8_qdiag : List ℚ :=
  [mkRat (.ofNat 19) 2, mkRat (.ofNat 489) 128, mkRat (.ofNat 663) 256, mkRat (.ofNat 129) 64,
      mkRat (.ofNat 455) 256, mkRat (.ofNat 219) 128, mkRat (.ofNat 267) 128,
      mkRat (.ofNat 1579) 256]

def lad8_qrem : List (List (ℕ × ℚ)) :=
  [[(0, mkRat (.ofNat 1) 2), (1, mkRat (.ofNat 7) 512), (2, mkRat (.negSucc 6) 512)],
    [(0, mkRat (.ofNat 7) 512), (1, mkRat (.ofNat 65813) 131072), (2, mkRat (.ofNat 763) 131072),
      (3, mkRat (.negSucc 132) 16384)],
    [(0, mkRat (.negSucc 6) 512), (1, mkRat (.ofNat 763) 131072), (2,
      mkRat (.ofNat 259435) 524288), (3, mkRat (.ofNat 3883) 1048576), (4,
      mkRat (.negSucc 128) 65536)],
    [(1, mkRat (.negSucc 132) 16384), (2, mkRat (.ofNat 3883) 1048576), (3,
      mkRat (.ofNat 8244009) 16777216), (4, mkRat (.ofNat 64125) 16777216), (5,
      mkRat (.ofNat 21) 8192)],
    [(2, mkRat (.negSucc 128) 65536), (3, mkRat (.ofNat 64125) 16777216), (4,
      mkRat (.ofNat 8309173) 16777216), (5, mkRat (.negSucc 2302) 2097152), (6,
      mkRat (.ofNat 29) 65536)],
    [(3, mkRat (.ofNat 21) 8192), (4, mkRat (.negSucc 2302) 2097152), (5,
      mkRat (.ofNat 2116381) 4194304), (6, mkRat (.negSucc 42326) 8388608), (7,
      mkRat (.negSucc 74) 32768)],
    [(4, mkRat (.ofNat 29) 65536), (5, mkRat (.negSucc 42326) 8388608), (6,
      mkRat (.ofNat 8454555) 16777216), (7, mkRat (.negSucc 11684) 8388608)],
    [(5, mkRat (.negSucc 74) 32768), (6, mkRat (.negSucc 11684) 8388608), (7,
      mkRat (.ofNat 4159509) 8388608)]]

def lad8_c : SparseLyapunovCert :=
  ⟨lad8_At, ⟨lad8_plower, lad8_pdiag, lad8_prem⟩, ⟨lad8_qlower, lad8_qdiag, lad8_qrem⟩⟩


def lad32_A : List (List (ℕ × ℚ)) :=
  [[(0, mkRat (.negSucc 0) 1), (1, mkRat (.negSucc 0) 1)],
    [(0, mkRat (.ofNat 1) 1), (2, mkRat (.negSucc 0) 1)],
    [(1, mkRat (.ofNat 1) 1), (3, mkRat (.negSucc 0) 1)],
    [(2, mkRat (.ofNat 1) 1), (4, mkRat (.negSucc 0) 1)],
    [(3, mkRat (.ofNat 1) 1), (5, mkRat (.negSucc 0) 1)],
    [(4, mkRat (.ofNat 1) 1), (6, mkRat (.negSucc 0) 1)],
    [(5, mkRat (.ofNat 1) 1), (7, mkRat (.negSucc 0) 1)],
    [(6, mkRat (.ofNat 1) 1), (8, mkRat (.negSucc 0) 1)],
    [(7, mkRat (.ofNat 1) 1), (9, mkRat (.negSucc 0) 1)],
    [(8, mkRat (.ofNat 1) 1), (10, mkRat (.negSucc 0) 1)],
    [(9, mkRat (.ofNat 1) 1), (11, mkRat (.negSucc 0) 1)],
    [(10, mkRat (.ofNat 1) 1), (12, mkRat (.negSucc 0) 1)],
    [(11, mkRat (.ofNat 1) 1), (13, mkRat (.negSucc 0) 1)],
    [(12, mkRat (.ofNat 1) 1), (14, mkRat (.negSucc 0) 1)],
    [(13, mkRat (.ofNat 1) 1), (15, mkRat (.negSucc 0) 1)],
    [(14, mkRat (.ofNat 1) 1), (16, mkRat (.negSucc 0) 1)],
    [(15, mkRat (.ofNat 1) 1), (17, mkRat (.negSucc 0) 1)],
    [(16, mkRat (.ofNat 1) 1), (18, mkRat (.negSucc 0) 1)],
    [(17, mkRat (.ofNat 1) 1), (19, mkRat (.negSucc 0) 1)],
    [(18, mkRat (.ofNat 1) 1), (20, mkRat (.negSucc 0) 1)],
    [(19, mkRat (.ofNat 1) 1), (21, mkRat (.negSucc 0) 1)],
    [(20, mkRat (.ofNat 1) 1), (22, mkRat (.negSucc 0) 1)],
    [(21, mkRat (.ofNat 1) 1), (23, mkRat (.negSucc 0) 1)],
    [(22, mkRat (.ofNat 1) 1), (24, mkRat (.negSucc 0) 1)],
    [(23, mkRat (.ofNat 1) 1), (25, mkRat (.negSucc 0) 1)],
    [(24, mkRat (.ofNat 1) 1), (26, mkRat (.negSucc 0) 1)],
    [(25, mkRat (.ofNat 1) 1), (27, mkRat (.negSucc 0) 1)],
    [(26, mkRat (.ofNat 1) 1), (28, mkRat (.negSucc 0) 1)],
    [(27, mkRat (.ofNat 1) 1), (29, mkRat (.negSucc 0) 1)],
    [(28, mkRat (.ofNat 1) 1), (30, mkRat (.negSucc 0) 1)],
    [(29, mkRat (.ofNat 1) 1), (31, mkRat (.negSucc 0) 1)],
    [(30, mkRat (.ofNat 1) 1), (31, mkRat (.negSucc 0) 1)]]

def lad32_P : List (List (ℕ × ℚ)) :=
  [[(0, mkRat (.ofNat 3999) 8), (1, mkRat (.ofNat 6455) 16)],
    [(0, mkRat (.ofNat 6455) 16), (1, mkRat (.ofNat 6933) 8), (2, mkRat (.ofNat 5769) 16)],
    [(1, mkRat (.ofNat 5769) 16), (2, mkRat (.ofNat 1709) 2), (3, mkRat (.ofNat 5263) 16)],
    [(2, mkRat (.ofNat 5263) 16), (3, mkRat (.ofNat 13635) 16), (4, mkRat (.ofNat 4815) 16)],
    [(3, mkRat (.ofNat 4815) 16), (4, mkRat (.ofNat 13627) 16), (5, mkRat (.ofNat 549) 2)],
    [(4, mkRat (.ofNat 549) 2), (5, mkRat (.ofNat 13625) 16), (6, mkRat (.ofNat 1991) 8)],
    [(5, mkRat (.ofNat 1991) 8), (6, mkRat (.ofNat 13625) 16), (7, mkRat (.ofNat 1789) 8)],
    [(6, mkRat (.ofNat 1789) 8), (7, mkRat (.ofNat 13625) 16), (8, mkRat (.ofNat 3177) 16)],
    [(7, mkRat (.ofNat 3177) 16), (8, mkRat (.ofNat 13625) 16), (9, mkRat (.ofNat 1389) 8)],
    [(8, mkRat (.ofNat 1389) 8), (9, mkRat (.ofNat 13625) 16), (10, mkRat (.ofNat 595) 4)],
    [(9, mkRat (.ofNat 595) 4), (10, mkRat (.ofNat 13625) 16), (11, mkRat (.ofNat 1983) 16)],
    [(10, mkRat (.ofNat 1983) 16), (11, mkRat (.ofNat 13625) 16), (12, mkRat (.ofNat 793) 8)],
    [(11, mkRat (.ofNat 793) 8), (12, mkRat (.ofNat 13625) 16), (13, mkRat (.ofNat 1189) 16)],
    [(12, mkRat (.ofNat 1189) 16), (13, mkRat (.ofNat 13625) 16), (14, mkRat (.ofNat 793) 16)],
    [(13, mkRat (.ofNat 793) 16), (14, mkRat (.ofNat 13625) 16), (15, mkRat (.ofNat 99) 4)],
    [(14, mkRat (.ofNat 99) 4), (15, mkRat (.ofNat 13625) 16)],
    [(16, mkRat (.ofNat 13625) 16), (17, mkRat (.negSucc 98) 4)],
    [(16, mkRat (.negSucc 98) 4), (17, mkRat (.ofNat 13625) 16), (18, mkRat (.negSucc 792) 16)],
    [(17, mkRat (.negSucc 792) 16), (18, mkRat (.ofNat 13625) 16), (19, mkRat (.negSucc 1188) 16)],
    [(18, mkRat (.negSucc 1188) 16), (19, mkRat (.ofNat 13625) 16), (20, mkRat (.negSucc 792) 8)],
    [(19, mkRat (.negSucc 792) 8), (20, mkRat (.ofNat 13625) 16), (21, mkRat (.negSucc 1982) 16)],
    [(20, mkRat (.negSucc 1982) 16), (21, mkRat (.ofNat 13625) 16), (22, mkRat (.negSucc 594) 4)],
    [(21, mkRat (.negSucc 594) 4), (22, mkRat (.ofNat 13625) 16), (23, mkRat (.negSucc 1388) 8)],
    [(22, mkRat (.negSucc 1388) 8), (23, mkRat (.ofNat 13625) 16), (24, mkRat (.negSucc 3176) 16)],
    [(23, mkRat (.negSucc 3176) 16), (24, mkRat (.ofNat 13625) 16), (25, mkRat (.negSucc 1788) 8)],
    [(24, mkRat (.negSucc 1788) 8), (25, mkRat (.ofNat 13625) 16), (26, mkRat (.negSucc 1990) 8)],
    [(25, mkRat (.negSucc 1990) 8), (26, mkRat (.ofNat 13625) 16), (27, mkRat (.negSucc 548) 2)],
    [(26, mkRat (.negSucc 548) 2), (27, mkRat (.ofNat 13627) 16), (28, mkRat (.negSucc 4814) 16)],
    [(27, mkRat (.negSucc 4814) 16), (28, mkRat (.ofNat 13635) 16), (29, mkRat (.negSucc 5262) 16)],
    [(28, mkRat (.negSucc 5262) 16), (29, mkRat (.ofNat 1709) 2), (30, mkRat (.negSucc 5768) 16)],
    [(29, mkRat (.negSucc 5768) 16), (30, mkRat (.ofNat 6933) 8), (31, mkRat (.negSucc 6454) 16)],
    [(30, mkRat (.negSucc 6454) 16), (31, mkRat (.ofNat 3999) 8)]]

def lad32_At : List (List (ℕ × ℚ)) :=
  [[(0, mkRat (.negSucc 0) 1), (1, mkRat (.ofNat 1) 1)],
    [(0, mkRat (.negSucc 0) 1), (2, mkRat (.ofNat 1) 1)],
    [(1, mkRat (.negSucc 0) 1), (3, mkRat (.ofNat 1) 1)],
    [(2, mkRat (.negSucc 0) 1), (4, mkRat (.ofNat 1) 1)],
    [(3, mkRat (.negSucc 0) 1), (5, mkRat (.ofNat 1) 1)],
    [(4, mkRat (.negSucc 0) 1), (6, mkRat (.ofNat 1) 1)],
    [(5, mkRat (.negSucc 0) 1), (7, mkRat (.ofNat 1) 1)],
    [(6, mkRat (.negSucc 0) 1), (8, mkRat (.ofNat 1) 1)],
    [(7, mkRat (.negSucc 0) 1), (9, mkRat (.ofNat 1) 1)],
    [(8, mkRat (.negSucc 0) 1), (10, mkRat (.ofNat 1) 1)],
    [(9, mkRat (.negSucc 0) 1), (11, mkRat (.ofNat 1) 1)],
    [(10, mkRat (.negSucc 0) 1), (12, mkRat (.ofNat 1) 1)],
    [(11, mkRat (.negSucc 0) 1), (13, mkRat (.ofNat 1) 1)],
    [(12, mkRat (.negSucc 0) 1), (14, mkRat (.ofNat 1) 1)],
    [(13, mkRat (.negSucc 0) 1), (15, mkRat (.ofNat 1) 1)],
    [(14, mkRat (.negSucc 0) 1), (16, mkRat (.ofNat 1) 1)],
    [(15, mkRat (.negSucc 0) 1), (17, mkRat (.ofNat 1) 1)],
    [(16, mkRat (.negSucc 0) 1), (18, mkRat (.ofNat 1) 1)],
    [(17, mkRat (.negSucc 0) 1), (19, mkRat (.ofNat 1) 1)],
    [(18, mkRat (.negSucc 0) 1), (20, mkRat (.ofNat 1) 1)],
    [(19, mkRat (.negSucc 0) 1), (21, mkRat (.ofNat 1) 1)],
    [(20, mkRat (.negSucc 0) 1), (22, mkRat (.ofNat 1) 1)],
    [(21, mkRat (.negSucc 0) 1), (23, mkRat (.ofNat 1) 1)],
    [(22, mkRat (.negSucc 0) 1), (24, mkRat (.ofNat 1) 1)],
    [(23, mkRat (.negSucc 0) 1), (25, mkRat (.ofNat 1) 1)],
    [(24, mkRat (.negSucc 0) 1), (26, mkRat (.ofNat 1) 1)],
    [(25, mkRat (.negSucc 0) 1), (27, mkRat (.ofNat 1) 1)],
    [(26, mkRat (.negSucc 0) 1), (28, mkRat (.ofNat 1) 1)],
    [(27, mkRat (.negSucc 0) 1), (29, mkRat (.ofNat 1) 1)],
    [(28, mkRat (.negSucc 0) 1), (30, mkRat (.ofNat 1) 1)],
    [(29, mkRat (.negSucc 0) 1), (31, mkRat (.ofNat 1) 1)],
    [(30, mkRat (.negSucc 0) 1), (31, mkRat (.negSucc 0) 1)]]

def lad32_plower : List (ℕ × List ℚ) :=
  [(0, [mkRat (.ofNat 1) 1]),
    (0, [mkRat (.ofNat 243) 256, mkRat (.ofNat 1) 1]),
    (1, [mkRat (.ofNat 225) 256, mkRat (.ofNat 1) 1]),
    (2, [mkRat (.ofNat 91) 128, mkRat (.ofNat 1) 1]),
    (3, [mkRat (.ofNat 141) 256, mkRat (.ofNat 1) 1]),
    (4, [mkRat (.ofNat 115) 256, mkRat (.ofNat 1) 1]),
    (5, [mkRat (.ofNat 97) 256, mkRat (.ofNat 1) 1]),
    (6, [mkRat (.ofNat 21) 64, mkRat (.ofNat 1) 1]),
    (7, [mkRat (.ofNat 9) 32, mkRat (.ofNat 1) 1]),
    (8, [mkRat (.ofNat 31) 128, mkRat (.ofNat 1) 1]),
    (9, [mkRat (.ofNat 13) 64, mkRat (.ofNat 1) 1]),
    (10, [mkRat (.ofNat 21) 128, mkRat (.ofNat 1) 1]),
    (11, [mkRat (.ofNat 17) 128, mkRat (.ofNat 1) 1]),
    (12, [mkRat (.ofNat 25) 256, mkRat (.ofNat 1) 1]),
    (13, [mkRat (.ofNat 1) 16, mkRat (.ofNat 1) 1]),
    (14, [mkRat (.ofNat 1) 32, mkRat (.ofNat 1) 1]),
    (16, [mkRat (.ofNat 1) 1]),
    (16, [mkRat (.negSucc 0) 32, mkRat (.ofNat 1) 1]),
    (17, [mkRat (.negSucc 0) 16, mkRat (.ofNat 1) 1]),
    (18, [mkRat (.negSucc 24) 256, mkRat (.ofNat 1) 1]),
    (19, [mkRat (.negSucc 32) 256, mkRat (.ofNat 1) 1]),
    (20, [mkRat (.negSucc 40) 256, mkRat (.ofNat 1) 1]),
    (21, [mkRat (.negSucc 24) 128, mkRat (.ofNat 1) 1]),
    (22, [mkRat (.negSucc 58) 256, mkRat (.ofNat 1) 1]),
    (23, [mkRat (.negSucc 68) 256, mkRat (.ofNat 1) 1]),
    (24, [mkRat (.negSucc 78) 256, mkRat (.ofNat 1) 1]),
    (25, [mkRat (.negSucc 44) 128, mkRat (.ofNat 1) 1]),
    (26, [mkRat (.negSucc 50) 128, mkRat (.ofNat 1) 1]),
    (27, [mkRat (.negSucc 114) 256, mkRat (.ofNat 1) 1]),
    (28, [mkRat (.negSucc 130) 256, mkRat (.ofNat 1) 1]),
    (29, [mkRat (.negSucc 150) 256, mkRat (.ofNat 1) 1]),
    (30, [mkRat (.negSucc 88) 128, mkRat (.ofNat 1) 1])]

def lad32_pdiag : List ℚ :=
  [mkRat (.ofNat 108997) 256, mkRat (.ofNat 52511) 128, mkRat (.ofNat 118655) 256,
      mkRat (.ofNat 34857) 64, mkRat (.ofNat 156493) 256, mkRat (.ofNat 83737) 128,
      mkRat (.ofNat 174791) 256, mkRat (.ofNat 180279) 256, mkRat (.ofNat 23087) 32,
      mkRat (.ofNat 47083) 64, mkRat (.ofNat 191329) 256, mkRat (.ofNat 24221) 32,
      mkRat (.ofNat 97853) 128, mkRat (.ofNat 49295) 64, mkRat (.ofNat 198213) 256,
      mkRat (.ofNat 99413) 128, mkRat (.ofNat 199029) 256, mkRat (.ofNat 198827) 256,
      mkRat (.ofNat 198219) 256, mkRat (.ofNat 197203) 256, mkRat (.ofNat 48941) 64,
      mkRat (.ofNat 193887) 256, mkRat (.ofNat 95775) 128, mkRat (.ofNat 188715) 256,
      mkRat (.ofNat 185337) 256, mkRat (.ofNat 90673) 128, mkRat (.ofNat 176645) 256,
      mkRat (.ofNat 85553) 128, mkRat (.ofNat 82251) 128, mkRat (.ofNat 156675) 256,
      mkRat (.ofNat 148505) 256, mkRat (.ofNat 37169) 256]

def lad32_prem : List (List (ℕ × ℚ)) :=
  [[(0, mkRat (.ofNat 18971) 256), (1, mkRat (.negSucc 46590) 65536)],
    [(0, mkRat (.negSucc 46590) 65536), (1, mkRat (.ofNat 1220669171) 16777216), (2,
      mkRat (.negSucc 62) 32768)],
    [(1, mkRat (.negSucc 62) 32768), (2, mkRat (.ofNat 621609121) 8388608), (3,
      mkRat (.negSucc 18980) 32768)],
    [(2, mkRat (.negSucc 18980) 32768), (3, mkRat (.ofNat 307363033) 4194304), (4,
      mkRat (.ofNat 15723) 16384)],
    [(3, mkRat (.ofNat 15723) 16384), (4, mkRat (.ofNat 315262959) 4194304), (5,
      mkRat (.negSucc 7062) 65536)],
    [(4, mkRat (.negSucc 7062) 65536), (5, mkRat (.ofNat 1241652011) 16777216), (6,
      mkRat (.ofNat 32647) 32768)],
    [(5, mkRat (.ofNat 32647) 32768), (6, mkRat (.ofNat 627991079) 8388608), (7,
      mkRat (.negSucc 6738) 16384)],
    [(6, mkRat (.negSucc 6738) 16384), (7, mkRat (.ofNat 77422385) 1048576), (8,
      mkRat (.ofNat 4113) 8192)],
    [(7, mkRat (.ofNat 4113) 8192), (8, mkRat (.ofNat 19500697) 262144), (9,
      mkRat (.negSucc 4528) 4096)],
    [(8, mkRat (.negSucc 4528) 4096), (9, mkRat (.ofNat 38573457) 524288), (10,
      mkRat (.negSucc 2798) 4096)],
    [(9, mkRat (.negSucc 2798) 4096), (10, mkRat (.ofNat 19354077) 262144), (11,
      mkRat (.ofNat 43275) 32768)],
    [(10, mkRat (.ofNat 43275) 32768), (11, mkRat (.ofNat 312640999) 4194304), (12,
      mkRat (.negSucc 5740) 4096)],
    [(11, mkRat (.negSucc 5740) 4096), (12, mkRat (.ofNat 38658243) 524288), (13,
      mkRat (.negSucc 11252) 32768)],
    [(12, mkRat (.negSucc 11252) 32768), (13, mkRat (.ofNat 621071635) 8388608), (14,
      mkRat (.ofNat 1457) 1024)],
    [(13, mkRat (.ofNat 1457) 1024), (14, mkRat (.ofNat 1217073) 16384), (15,
      mkRat (.ofNat 4539) 8192)],
    [(14, mkRat (.ofNat 4539) 8192), (15, mkRat (.ofNat 19435963) 262144)],
    [(16, mkRat (.ofNat 18971) 256), (17, mkRat (.negSucc 3722) 8192)],
    [(16, mkRat (.negSucc 3722) 8192), (17, mkRat (.ofNat 19434123) 262144), (18,
      mkRat (.negSucc 4180) 4096)],
    [(17, mkRat (.negSucc 4180) 4096), (18, mkRat (.ofNat 4865109) 65536), (19,
      mkRat (.ofNat 85331) 65536)],
    [(18, mkRat (.ofNat 85331) 65536), (19, mkRat (.ofNat 1239065317) 16777216), (20,
      mkRat (.ofNat 11443) 65536)],
    [(19, mkRat (.ofNat 11443) 65536), (20, mkRat (.ofNat 1242504429) 16777216), (21,
      mkRat (.negSucc 24010) 16384)],
    [(20, mkRat (.negSucc 24010) 16384), (21, mkRat (.ofNat 312797571) 4194304), (22,
      mkRat (.negSucc 27064) 32768)],
    [(21, mkRat (.negSucc 27064) 32768), (22, mkRat (.ofNat 312177425) 4194304), (23,
      mkRat (.negSucc 38618) 32768)],
    [(22, mkRat (.negSucc 38618) 32768), (23, mkRat (.ofNat 626218105) 8388608), (24,
      mkRat (.ofNat 8343) 65536)],
    [(23, mkRat (.ofNat 8343) 65536), (24, mkRat (.ofNat 1242130253) 16777216), (25,
      mkRat (.negSucc 13864) 65536)],
    [(24, mkRat (.negSucc 13864) 65536), (25, mkRat (.ofNat 1245468327) 16777216), (26,
      mkRat (.ofNat 2717) 16384)],
    [(25, mkRat (.ofNat 2717) 16384), (26, mkRat (.ofNat 155167335) 2097152), (27,
      mkRat (.ofNat 14079) 32768)],
    [(26, mkRat (.ofNat 14079) 32768), (27, mkRat (.ofNat 309381939) 4194304), (28,
      mkRat (.negSucc 22524) 32768)],
    [(27, mkRat (.negSucc 22524) 32768), (28, mkRat (.ofNat 626826919) 8388608), (29,
      mkRat (.negSucc 3742) 32768)],
    [(28, mkRat (.negSucc 3742) 32768), (29, mkRat (.ofNat 622629725) 8388608), (30,
      mkRat (.ofNat 28101) 65536)],
    [(29, mkRat (.ofNat 28101) 65536), (30, mkRat (.ofNat 1234784461) 16777216), (31,
      mkRat (.negSucc 2894) 32768)],
    [(30, mkRat (.negSucc 2894) 32768), (31, mkRat (.ofNat 311342711) 4194304)]]

def lad32_qlower : List (ℕ × List ℚ) :=
  [(0, [mkRat (.ofNat 1) 1]),
    (0, [mkRat (.ofNat 49) 256, mkRat (.ofNat 1) 1]),
    (0, [mkRat (.ofNat 57) 256, mkRat (.ofNat 13) 256, mkRat (.ofNat 1) 1]),
    (1, [mkRat (.ofNat 103) 256, mkRat (.ofNat 3) 256, mkRat (.ofNat 1) 1]),
    (2, [mkRat (.ofNat 135) 256, mkRat (.ofNat 1) 256, mkRat (.ofNat 1) 1]),
    (3, [mkRat (.ofNat 79) 128, mkRat (.ofNat 0) 1, mkRat (.ofNat 1) 1]),
    (4, [mkRat (.ofNat 175) 256, mkRat (.ofNat 0) 1, mkRat (.ofNat 1) 1]),
    (5, [mkRat (.ofNat 47) 64, mkRat (.ofNat 0) 1, mkRat (.ofNat 1) 1]),
    (6, [mkRat (.ofNat 197) 256, mkRat (.ofNat 0) 1, mkRat (.ofNat 1) 1]),
    (7, [mkRat (.ofNat 205) 256, mkRat (.ofNat 0) 1, mkRat (.ofNat 1) 1]),
    (8, [mkRat (.ofNat 53) 64, mkRat (.ofNat 0) 1, mkRat (.ofNat 1) 1]),
    (9, [mkRat (.ofNat 217) 256, mkRat (.ofNat 0) 1, mkRat (.ofNat 1) 1]),
    (10, [mkRat (.ofNat 223) 256, mkRat (.ofNat 0) 1, mkRat (.ofNat 1) 1]),
    (11, [mkRat (.ofNat 113) 128, mkRat (.ofNat 0) 1, mkRat (.ofNat 1) 1]),
    (12, [mkRat (.ofNat 115) 128, mkRat (.ofNat 0) 1, mkRat (.ofNat 1) 1]),
    (13, [mkRat (.ofNat 235) 256, mkRat (.ofNat 0) 1, mkRat (.ofNat 1) 1]),
    (14, [mkRat (.ofNat 59) 64, mkRat (.ofNat 0) 1, mkRat (.ofNat 1) 1]),
    (15, [mkRat (.ofNat 241) 256, mkRat (.ofNat 0) 1, mkRat (.ofNat 1) 1]),
    (16, [mkRat (.ofNat 121) 128, mkRat (.ofNat 0) 1, mkRat (.ofNat 1) 1]),
    (17, [mkRat (.ofNat 123) 128, mkRat (.ofNat 0) 1, mkRat (.ofNat 1) 1]),
    (18, [mkRat (.ofNat 249) 256, mkRat (.ofNat 0) 1, mkRat (.ofNat 1) 1]),
    (19, [mkRat (.ofNat 125) 128, mkRat (.ofNat 0) 1, mkRat (.ofNat 1) 1]),
    (20, [mkRat (.ofNat 127) 128, mkRat (.ofNat 0) 1, mkRat (.ofNat 1) 1]),
    (21, [mkRat (.ofNat 1) 1, mkRat (.ofNat 0) 1, mkRat (.ofNat 1) 1]),
    (22, [mkRat (.ofNat 259) 256, mkRat (.ofNat 0) 1, mkRat (.ofNat 1) 1]),
    (23, [mkRat (.ofNat 131) 128, mkRat (.ofNat 0) 1, mkRat (.ofNat 1) 1]),
    (24, [mkRat (.ofNat 265) 256, mkRat (.ofNat 0) 1, mkRat (.ofNat 1) 1]),
    (25, [mkRat (.ofNat 269) 256, mkRat (.negSucc 0) 256, mkRat (.ofNat 1) 1]),
    (26, [mkRat (.ofNat 275) 256, mkRat (.negSucc 0) 64, mkRat (.ofNat 1) 1]),
    (27, [mkRat (.ofNat 141) 128, mkRat (.negSucc 8) 128, mkRat (.ofNat 1) 1]),
    (28, [mkRat (.ofNat 299) 256, mkRat (.negSucc 4) 16, mkRat (.ofNat 1) 1]),
    (29, [mkRat (.ofNat 173) 128, mkRat (.negSucc 32) 64, mkRat (.ofNat 1) 1])]

def lad32_qdiag : List ℚ :=
  [mkRat (.ofNat 1539) 8, mkRat (.ofNat 20033) 256, mkRat (.ofNat 13567) 256,
      mkRat (.ofNat 5467) 128, mkRat (.ofNat 9621) 256, mkRat (.ofNat 8803) 256,
      mkRat (.ofNat 8327) 256, mkRat (.ofNat 7957) 256, mkRat (.ofNat 481) 16,
      mkRat (.ofNat 3743) 128, mkRat (.ofNat 7307) 256, mkRat (.ofNat 3593) 128,
      mkRat (.ofNat 3527) 128, mkRat (.ofNat 3465) 128, mkRat (.ofNat 6885) 256,
      mkRat (.ofNat 6721) 256, mkRat (.ofNat 6713) 256, mkRat (.ofNat 6603) 256,
      mkRat (.ofNat 3267) 128, mkRat (.ofNat 6497) 256, mkRat (.ofNat 6401) 256,
      mkRat (.ofNat 6365) 256, mkRat (.ofNat 6305) 256, mkRat (.ofNat 6269) 256,
      mkRat (.ofNat 195) 8, mkRat (.ofNat 3117) 128, mkRat (.ofNat 787) 32,
      mkRat (.ofNat 6505) 256, mkRat (.ofNat 6931) 256, mkRat (.ofNat 8131) 256,
      mkRat (.ofNat 11577) 256, mkRat (.ofNat 31353) 256]

def lad32_qrem : List (List (ℕ × ℚ)) :=
  [[(0, mkRat (.ofNat 1) 2), (1, mkRat (.negSucc 274) 2048), (2, mkRat (.ofNat 85) 2048)],
    [(0, mkRat (.negSucc 274) 2048), (1, mkRat (.ofNat 234973) 524288), (2,
      mkRat (.negSucc 24866) 524288), (3, mkRat (.ofNat 9177) 65536)],
    [(0, mkRat (.ofNat 85) 2048), (1, mkRat (.negSucc 24866) 524288), (2,
      mkRat (.ofNat 8639671) 16777216), (3, mkRat (.ofNat 1553669) 16777216), (4,
      mkRat (.ofNat 3463) 65536)],
    [(1, mkRat (.ofNat 9177) 65536), (2, mkRat (.ofNat 1553669) 16777216), (3,
      mkRat (.ofNat 1287659) 2097152), (4, mkRat (.ofNat 94869) 16777216), (5,
      mkRat (.ofNat 1259) 16384)],
    [(2, mkRat (.ofNat 3463) 65536), (3, mkRat (.ofNat 94869) 16777216), (4,
      mkRat (.ofNat 9303931) 16777216), (5, mkRat (.ofNat 92395) 4194304), (6,
      mkRat (.negSucc 4314) 65536)],
    [(3, mkRat (.ofNat 1259) 16384), (4, mkRat (.ofNat 92395) 4194304), (5,
      mkRat (.ofNat 1245317) 2097152), (7, mkRat (.negSucc 44) 16384)],
    [(4, mkRat (.negSucc 4314) 65536), (6, mkRat (.ofNat 6888011) 16777216), (8,
      mkRat (.ofNat 2077) 65536)],
    [(5, mkRat (.negSucc 44) 16384), (7, mkRat (.ofNat 522173) 1048576), (9,
      mkRat (.ofNat 3119) 65536)],
    [(6, mkRat (.ofNat 2077) 65536), (8, mkRat (.ofNat 9236049) 16777216), (10,
      mkRat (.negSucc 20) 1024)],
    [(7, mkRat (.ofNat 3119) 65536), (9, mkRat (.ofNat 9671075) 16777216), (11,
      mkRat (.ofNat 825) 32768)],
    [(8, mkRat (.negSucc 20) 1024), (10, mkRat (.ofNat 30503) 65536), (12,
      mkRat (.negSucc 3348) 65536)],
    [(9, mkRat (.ofNat 825) 32768), (11, mkRat (.ofNat 4559697) 8388608), (13,
      mkRat (.ofNat 519) 16384)],
    [(10, mkRat (.negSucc 3348) 65536), (12, mkRat (.ofNat 6908597) 16777216), (14,
      mkRat (.negSucc 100) 16384)],
    [(11, mkRat (.ofNat 519) 16384), (13, mkRat (.ofNat 1159447) 2097152), (15,
      mkRat (.negSucc 1218) 32768)],
    [(12, mkRat (.negSucc 100) 16384), (14, mkRat (.ofNat 1024673) 2097152), (16,
      mkRat (.negSucc 710) 16384)],
    [(13, mkRat (.negSucc 1218) 32768), (15, mkRat (.ofNat 3647743) 8388608), (17,
      mkRat (.ofNat 2255) 65536)],
    [(14, mkRat (.negSucc 710) 16384), (16, mkRat (.ofNat 441379) 1048576), (18,
      mkRat (.ofNat 783) 32768)],
    [(15, mkRat (.ofNat 2255) 65536), (17, mkRat (.ofNat 9472735) 16777216), (19,
      mkRat (.negSucc 1160) 32768)],
    [(16, mkRat (.ofNat 783) 32768), (18, mkRat (.ofNat 2279959) 4194304), (20,
      mkRat (.negSucc 426) 32768)],
    [(17, mkRat (.negSucc 1160) 32768), (19, mkRat (.ofNat 1798701) 4194304), (21,
      mkRat (.ofNat 931) 32768)],
    [(18, mkRat (.negSucc 426) 32768), (20, mkRat (.ofNat 3979437) 8388608), (22,
      mkRat (.ofNat 129) 32768)],
    [(19, mkRat (.ofNat 931) 32768), (21, mkRat (.ofNat 2342551) 4194304), (23,
      mkRat (.ofNat 3) 256)],
    [(20, mkRat (.ofNat 129) 32768), (22, mkRat (.ofNat 2123775) 4194304), (24,
      mkRat (.ofNat 1309) 65536)],
    [(21, mkRat (.ofNat 3) 256), (23, mkRat (.ofNat 67) 128), (25, mkRat (.ofNat 9) 32768)],
    [(22, mkRat (.ofNat 1309) 65536), (24, mkRat (.ofNat 9067607) 16777216), (26,
      mkRat (.ofNat 37) 2048)],
    [(23, mkRat (.ofNat 9) 32768), (25, mkRat (.ofNat 2092187) 4194304), (27,
      mkRat (.ofNat 1207) 32768)],
    [(24, mkRat (.ofNat 37) 2048), (26, mkRat (.ofNat 281677) 524288), (27,
      mkRat (.negSucc 236) 8192), (28, mkRat (.ofNat 151) 8192)],
    [(25, mkRat (.ofNat 1207) 32768), (26, mkRat (.negSucc 236) 8192), (27,
      mkRat (.ofNat 4839423) 8388608), (28, mkRat (.ofNat 489) 2097152), (29,
      mkRat (.ofNat 299) 32768)],
    [(26, mkRat (.ofNat 151) 8192), (27, mkRat (.ofNat 489) 2097152), (28,
      mkRat (.ofNat 1131875) 2097152), (29, mkRat (.ofNat 59797) 2097152), (30,
      mkRat (.ofNat 207) 65536)],
    [(27, mkRat (.ofNat 299) 32768), (28, mkRat (.ofNat 59797) 2097152), (29,
      mkRat (.ofNat 546027) 1048576), (30, mkRat (.ofNat 200889) 8388608), (31,
      mkRat (.negSucc 1734) 32768)],
    [(28, mkRat (.ofNat 207) 65536), (29, mkRat (.ofNat 200889) 8388608), (30,
      mkRat (.ofNat 8259269) 16777216), (31, mkRat (.ofNat 23811) 524288)],
    [(29, mkRat (.negSucc 1734) 32768), (30, mkRat (.ofNat 23811) 524288), (31,
      mkRat (.ofNat 1506721) 4194304)]]

def lad32_c : SparseLyapunovCert :=
  ⟨lad32_At, ⟨lad32_plower, lad32_pdiag, lad32_prem⟩, ⟨lad32_qlower, lad32_qdiag, lad32_qrem⟩⟩


def tree15_A : List (List (ℕ × ℚ)) :=
  [[(0, mkRat (.negSucc 0) 1), (2, mkRat (.ofNat 1) 1)],
    [(1, mkRat (.negSucc 0) 1), (2, mkRat (.ofNat 1) 1)],
    [(0, mkRat (.ofNat 1) 1), (1, mkRat (.ofNat 1) 1), (2, mkRat (.negSucc 2) 1), (6,
      mkRat (.ofNat 1) 1)],
    [(3, mkRat (.negSucc 0) 1), (5, mkRat (.ofNat 1) 1)],
    [(4, mkRat (.negSucc 0) 1), (5, mkRat (.ofNat 1) 1)],
    [(3, mkRat (.ofNat 1) 1), (4, mkRat (.ofNat 1) 1), (5, mkRat (.negSucc 2) 1), (6,
      mkRat (.ofNat 1) 1)],
    [(2, mkRat (.ofNat 1) 1), (5, mkRat (.ofNat 1) 1), (6, mkRat (.negSucc 2) 1), (14,
      mkRat (.ofNat 1) 1)],
    [(7, mkRat (.negSucc 0) 1), (9, mkRat (.ofNat 1) 1)],
    [(8, mkRat (.negSucc 0) 1), (9, mkRat (.ofNat 1) 1)],
    [(7, mkRat (.ofNat 1) 1), (8, mkRat (.ofNat 1) 1), (9, mkRat (.negSucc 2) 1), (13,
      mkRat (.ofNat 1) 1)],
    [(10, mkRat (.negSucc 0) 1), (12, mkRat (.ofNat 1) 1)],
    [(11, mkRat (.negSucc 0) 1), (12, mkRat (.ofNat 1) 1)],
    [(10, mkRat (.ofNat 1) 1), (11, mkRat (.ofNat 1) 1), (12, mkRat (.negSucc 2) 1), (13,
      mkRat (.ofNat 1) 1)],
    [(9, mkRat (.ofNat 1) 1), (12, mkRat (.ofNat 1) 1), (13, mkRat (.negSucc 2) 1), (14,
      mkRat (.ofNat 1) 1)],
    [(6, mkRat (.ofNat 1) 1), (13, mkRat (.ofNat 1) 1), (14, mkRat (.negSucc 2) 1)]]

def tree15_P : List (List (ℕ × ℚ)) :=
  [[(0, mkRat (.ofNat 1) 1)],
    [(1, mkRat (.ofNat 1) 1)],
    [(2, mkRat (.ofNat 1) 1)],
    [(3, mkRat (.ofNat 1) 1)],
    [(4, mkRat (.ofNat 1) 1)],
    [(5, mkRat (.ofNat 1) 1)],
    [(6, mkRat (.ofNat 1) 1)],
    [(7, mkRat (.ofNat 1) 1)],
    [(8, mkRat (.ofNat 1) 1)],
    [(9, mkRat (.ofNat 1) 1)],
    [(10, mkRat (.ofNat 1) 1)],
    [(11, mkRat (.ofNat 1) 1)],
    [(12, mkRat (.ofNat 1) 1)],
    [(13, mkRat (.ofNat 1) 1)],
    [(14, mkRat (.ofNat 1) 1)]]

def tree15_At : List (List (ℕ × ℚ)) :=
  [[(0, mkRat (.negSucc 0) 1), (2, mkRat (.ofNat 1) 1)],
    [(1, mkRat (.negSucc 0) 1), (2, mkRat (.ofNat 1) 1)],
    [(0, mkRat (.ofNat 1) 1), (1, mkRat (.ofNat 1) 1), (2, mkRat (.negSucc 2) 1), (6,
      mkRat (.ofNat 1) 1)],
    [(3, mkRat (.negSucc 0) 1), (5, mkRat (.ofNat 1) 1)],
    [(4, mkRat (.negSucc 0) 1), (5, mkRat (.ofNat 1) 1)],
    [(3, mkRat (.ofNat 1) 1), (4, mkRat (.ofNat 1) 1), (5, mkRat (.negSucc 2) 1), (6,
      mkRat (.ofNat 1) 1)],
    [(2, mkRat (.ofNat 1) 1), (5, mkRat (.ofNat 1) 1), (6, mkRat (.negSucc 2) 1), (14,
      mkRat (.ofNat 1) 1)],
    [(7, mkRat (.negSucc 0) 1), (9, mkRat (.ofNat 1) 1)],
    [(8, mkRat (.negSucc 0) 1), (9, mkRat (.ofNat 1) 1)],
    [(7, mkRat (.ofNat 1) 1), (8, mkRat (.ofNat 1) 1), (9, mkRat (.negSucc 2) 1), (13,
      mkRat (.ofNat 1) 1)],
    [(10, mkRat (.negSucc 0) 1), (12, mkRat (.ofNat 1) 1)],
    [(11, mkRat (.negSucc 0) 1), (12, mkRat (.ofNat 1) 1)],
    [(10, mkRat (.ofNat 1) 1), (11, mkRat (.ofNat 1) 1), (12, mkRat (.negSucc 2) 1), (13,
      mkRat (.ofNat 1) 1)],
    [(9, mkRat (.ofNat 1) 1), (12, mkRat (.ofNat 1) 1), (13, mkRat (.negSucc 2) 1), (14,
      mkRat (.ofNat 1) 1)],
    [(6, mkRat (.ofNat 1) 1), (13, mkRat (.ofNat 1) 1), (14, mkRat (.negSucc 2) 1)]]

def tree15_plower : List (ℕ × List ℚ) :=
  [(0, [mkRat (.ofNat 1) 1]),
    (1, [mkRat (.ofNat 1) 1]),
    (2, [mkRat (.ofNat 1) 1]),
    (3, [mkRat (.ofNat 1) 1]),
    (4, [mkRat (.ofNat 1) 1]),
    (5, [mkRat (.ofNat 1) 1]),
    (6, [mkRat (.ofNat 1) 1]),
    (7, [mkRat (.ofNat 1) 1]),
    (8, [mkRat (.ofNat 1) 1]),
    (9, [mkRat (.ofNat 1) 1]),
    (10, [mkRat (.ofNat 1) 1]),
    (11, [mkRat (.ofNat 1) 1]),
    (12, [mkRat (.ofNat 1) 1]),
    (13, [mkRat (.ofNat 1) 1]),
    (14, [mkRat (.ofNat 1) 1])]

def tree15_pdiag : List ℚ :=
  [mkRat (.ofNat 1) 2, mkRat (.ofNat 1) 2, mkRat (.ofNat 1) 2, mkRat (.ofNat 1) 2,
      mkRat (.ofNat 1) 2, mkRat (.ofNat 1) 2, mkRat (.ofNat 1) 2, mkRat (.ofNat 1) 2,
      mkRat (.ofNat 1) 2, mkRat (.ofNat 1) 2, mkRat (.ofNat 1) 2, mkRat (.ofNat 1) 2,
      mkRat (.ofNat 1) 2, mkRat (.ofNat 1) 2, mkRat (.ofNat 1) 2]

def tree15_prem : List (List (ℕ × ℚ)) :=
  [[(0, mkRat (.ofNat 1) 2)],
    [(1, mkRat (.ofNat 1) 2)],
    [(2, mkRat (.ofNat 1) 2)],
    [(3, mkRat (.ofNat 1) 2)],
    [(4, mkRat (.ofNat 1) 2)],
    [(5, mkRat (.ofNat 1) 2)],
    [(6, mkRat (.ofNat 1) 2)],
    [(7, mkRat (.ofNat 1) 2)],
    [(8, mkRat (.ofNat 1) 2)],
    [(9, mkRat (.ofNat 1) 2)],
    [(10, mkRat (.ofNat 1) 2)],
    [(11, mkRat (.ofNat 1) 2)],
    [(12, mkRat (.ofNat 1) 2)],
    [(13, mkRat (.ofNat 1) 2)],
    [(14, mkRat (.ofNat 1) 2)]]

def tree15_qlower : List (ℕ × List ℚ) :=
  [(0, [mkRat (.ofNat 1) 1]),
    (1, [mkRat (.ofNat 1) 1]),
    (0, [mkRat (.negSucc 260) 256, mkRat (.negSucc 260) 256, mkRat (.ofNat 1) 1]),
    (3, [mkRat (.ofNat 1) 1]),
    (4, [mkRat (.ofNat 1) 1]),
    (3, [mkRat (.negSucc 260) 256, mkRat (.negSucc 260) 256, mkRat (.ofNat 1) 1]),
    (2, [mkRat (.negSucc 272) 256, mkRat (.ofNat 0) 1, mkRat (.ofNat 0) 1,
      mkRat (.negSucc 272) 256, mkRat (.ofNat 1) 1]),
    (7, [mkRat (.ofNat 1) 1]),
    (8, [mkRat (.ofNat 1) 1]),
    (7, [mkRat (.negSucc 260) 256, mkRat (.negSucc 260) 256, mkRat (.ofNat 1) 1]),
    (10, [mkRat (.ofNat 1) 1]),
    (11, [mkRat (.ofNat 1) 1]),
    (10, [mkRat (.negSucc 260) 256, mkRat (.negSucc 260) 256, mkRat (.ofNat 1) 1]),
    (9, [mkRat (.negSucc 272) 256, mkRat (.ofNat 0) 1, mkRat (.ofNat 0) 1,
      mkRat (.negSucc 272) 256, mkRat (.ofNat 1) 1]),
    (6, [mkRat (.negSucc 300) 256, mkRat (.ofNat 0) 1, mkRat (.ofNat 0) 1, mkRat (.ofNat 0) 1,
      mkRat (.ofNat 0) 1, mkRat (.ofNat 0) 1, mkRat (.ofNat 0) 1, mkRat (.negSucc 300) 256,
      mkRat (.ofNat 1) 1])]

def tree15_qdiag : List ℚ :=
  [mkRat (.ofNat 251) 128, mkRat (.ofNat 251) 128, mkRat (.ofNat 481) 256, mkRat (.ofNat 251) 128,
      mkRat (.ofNat 251) 128, mkRat (.ofNat 481) 256, mkRat (.ofNat 435) 256,
      mkRat (.ofNat 251) 128, mkRat (.ofNat 251) 128, mkRat (.ofNat 481) 256,
      mkRat (.ofNat 251) 128, mkRat (.ofNat 251) 128, mkRat (.ofNat 481) 256,
      mkRat (.ofNat 435) 256, mkRat (.ofNat 5) 4]

def tree15_qrem : List (List (ℕ × ℚ)) :=
  [[(0, mkRat (.ofNat 5) 128), (2, mkRat (.negSucc 24) 32768)],
    [(1, mkRat (.ofNat 5) 128), (2, mkRat (.negSucc 24) 32768)],
    [(0, mkRat (.negSucc 24) 32768), (1, mkRat (.negSucc 24) 32768), (2,
      mkRat (.ofNat 186749) 4194304), (6, mkRat (.ofNat 241) 65536)],
    [(3, mkRat (.ofNat 5) 128), (5, mkRat (.negSucc 24) 32768)],
    [(4, mkRat (.ofNat 5) 128), (5, mkRat (.negSucc 24) 32768)],
    [(3, mkRat (.negSucc 24) 32768), (4, mkRat (.negSucc 24) 32768), (5,
      mkRat (.ofNat 186749) 4194304), (6, mkRat (.ofNat 241) 65536)],
    [(2, mkRat (.ofNat 241) 65536), (5, mkRat (.ofNat 241) 65536), (6,
      mkRat (.ofNat 229119) 8388608), (14, mkRat (.negSucc 136) 65536)],
    [(7, mkRat (.ofNat 5) 128), (9, mkRat (.negSucc 24) 32768)],
    [(8, mkRat (.ofNat 5) 128), (9, mkRat (.negSucc 24) 32768)],
    [(7, mkRat (.negSucc 24) 32768), (8, mkRat (.negSucc 24) 32768), (9,
      mkRat (.ofNat 186749) 4194304), (13, mkRat (.ofNat 241) 65536)],
    [(10, mkRat (.ofNat 5) 128), (12, mkRat (.negSucc 24) 32768)],
    [(11, mkRat (.ofNat 5) 128), (12, mkRat (.negSucc 24) 32768)],
    [(10, mkRat (.negSucc 24) 32768), (11, mkRat (.negSucc 24) 32768), (12,
      mkRat (.ofNat 186749) 4194304), (13, mkRat (.ofNat 241) 65536)],
    [(9, mkRat (.ofNat 241) 65536), (12, mkRat (.ofNat 241) 65536), (13,
      mkRat (.ofNat 229119) 8388608), (14, mkRat (.negSucc 136) 65536)],
    [(6, mkRat (.negSucc 136) 65536), (13, mkRat (.negSucc 136) 65536), (14,
      mkRat (.ofNat 434453) 8388608)]]

def tree15_c : SparseLyapunovCert :=
  ⟨tree15_At, ⟨tree15_plower, tree15_pdiag, tree15_prem⟩, ⟨tree15_qlower, tree15_qdiag,
      tree15_qrem⟩⟩

theorem lad8_ok : lad8_c.check 8 lad8_A lad8_P = true := by decide +kernel

theorem lad32_ok : lad32_c.check 32 lad32_A lad32_P = true := by decide +kernel

theorem tree15_ok : tree15_c.check 15 tree15_A tree15_P = true := by decide +kernel

end Cslib.LinearAlgebra.SparseLDLCertificateTests
