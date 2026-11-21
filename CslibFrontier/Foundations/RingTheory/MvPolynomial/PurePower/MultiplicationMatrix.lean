/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate (Mathlib, pure-power polynomial quotients and multiplication matrices)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.Trace

/-!
# Multiplication matrices in the normal-monomial basis

`multiplicationMatrix` represents multiplication in the actual pure-power quotient, using its
proved normal-monomial basis indexed by `Fin n → Fin ell`. Its power traces are finite residues
against the Jacobian polynomial (`multiplicationMatrix_trace_pow`). Applying any coefficient
homomorphism to the matrix gives the corresponding specialized residue formula
(`multiplicationMatrix_map_trace_pow`), without constructing a specialized basis or requiring
injectivity or simple roots. The coefficient rings are arbitrary commutative rings.

The matrix is a mathematical specification; it is not expanded machine input. This module
asserts no complexity bound. The construction and identities are adapted from
[normal-basis multiplication matrices](https://github.com/edemaine/lean-canny/blob/970f28a5ecefc1327402ade16c068aa4b1b2c183/LeanCanny/CountingHierarchy/QuotientMultiplicationMatrix.lean)
and
[trace specialization](https://github.com/edemaine/lean-canny/blob/970f28a5ecefc1327402ade16c068aa4b1b2c183/LeanCanny/CountingHierarchy/QuotientTraceSpecialization.lean)
in lean-canny.
-/

public section

namespace MvPolynomial.PurePower

variable {S T : Type*} [CommRing S] [CommRing T] {n ell : ℕ}

open Classical in
/-- Multiplication in the proved normal-monomial basis, as an algebra homomorphism. -/
noncomputable def multiplicationMatrix (hell : 1 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree < ell) :
    MvPolynomial (Fin n) S →ₐ[S] Matrix (NormalIndex n ell) (NormalIndex n ell) S :=
  (Algebra.leftMulMatrix (normalBasis hell r hr)).comp (projection ell r)

/-- Power traces are residues against the Jacobian, including at multiple roots. -/
theorem multiplicationMatrix_trace_pow (d : ℕ) (hd : 1 ≤ d)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree ≤ d)
    (v : MvPolynomial (Fin n) S) (k : ℕ) :
    ((multiplicationMatrix (by omega : 1 ≤ d + 1) r
      (fun i => (hr i).trans_lt (Nat.lt_succ_self d)) v) ^ k).trace =
        residue (d + 1) r (v ^ k * jacobian (d + 1) r) := by
  classical
  rw [← map_pow]
  change (Algebra.leftMulMatrix (normalBasis _ r _) (projection (d + 1) r (v ^ k))).trace = _
  rw [← Algebra.trace_eq_matrix_trace]
  exact trace_eq_residue d hd r hr (v ^ k)

/-- Source matrix power traces specialize to the same finite residue formula. No change of
basis between source and specialized quotient presentations is needed. -/
theorem multiplicationMatrix_map_trace_pow (φ : S →+* T)
    (d : ℕ) (hd : 1 ≤ d)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree ≤ d)
    (v : MvPolynomial (Fin n) S) (k : ℕ) :
    (((multiplicationMatrix (by omega : 1 ≤ d + 1) r
      (fun i => (hr i).trans_lt (Nat.lt_succ_self d)) v).map φ) ^ k).trace =
        residue (d + 1) (fun i => (r i).map φ)
          ((v.map φ) ^ k * jacobian (d + 1) (fun i => (r i).map φ)) := by
  classical
  rw [← Matrix.map_pow, ← AddMonoidHom.map_trace,
    multiplicationMatrix_trace_pow d hd r hr v k,
    residue_map φ (by omega) r (fun i => (hr i).trans_lt (Nat.lt_succ_self d)),
    map_mul, map_pow, jacobian_map]

end MvPolynomial.PurePower
