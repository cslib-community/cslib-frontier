/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate (Mathlib, pure-power polynomial quotients and multiplication matrices)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.Trace
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Multiplication matrices in the normal-monomial basis

`multiplicationMatrix` represents multiplication in the actual pure-power quotient, using its
proved normal-monomial basis indexed by `Fin n → Fin ell`. Its entries commute with
coefficient maps (`multiplicationMatrix_map`). Its power traces are finite residues
against the Jacobian polynomial (`multiplicationMatrix_trace_pow`). Applying any coefficient
homomorphism to the matrix gives the corresponding specialized residue formula
(`multiplicationMatrix_map_trace_pow`), without constructing a specialized basis or requiring
injectivity or simple roots. The coefficient rings are arbitrary commutative rings.
Evaluating the relations at a common zero yields a characteristic root by Cayley–Hamilton.

The matrix is a mathematical specification; it is not expanded machine input. This module
asserts no complexity bound. The construction and identities are adapted from
[normal-basis multiplication matrices](https://github.com/edemaine/lean-canny/blob/970f28a5ecefc1327402ade16c068aa4b1b2c183/LeanCanny/CountingHierarchy/QuotientMultiplicationMatrix.lean)
and
[trace specialization](https://github.com/edemaine/lean-canny/blob/970f28a5ecefc1327402ade16c068aa4b1b2c183/LeanCanny/CountingHierarchy/QuotientTraceSpecialization.lean)
in lean-canny. The characteristic-root argument is adapted from `QuotientEvaluation` at
the same revision.
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

/-- Polynomials that represent the same quotient element give the same multiplication matrix. -/
theorem multiplicationMatrix_eq_of_projection_eq (hell : 1 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree < ell)
    {v w : MvPolynomial (Fin n) S} (h : projection ell r v = projection ell r w) :
    multiplicationMatrix hell r hr v = multiplicationMatrix hell r hr w :=
  congrArg (Algebra.leftMulMatrix (normalBasis hell r hr)) h

/-- The normal monomial coordinates of multiplication commute with every coefficient map. -/
theorem multiplicationMatrix_map (φ : S →+* T) (hell : 1 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree < ell)
    (v : MvPolynomial (Fin n) S) :
    (multiplicationMatrix hell r hr v).map φ =
      multiplicationMatrix hell (fun i => (r i).map φ)
        (fun i => (totalDegree_map_le φ (r i)).trans_lt (hr i)) (v.map φ) := by
  classical
  let r' : Fin n → MvPolynomial (Fin n) T := fun i => (r i).map φ
  have hr' (i : Fin n) : (r' i).totalDegree < ell :=
    (totalDegree_map_le φ (r i)).trans_lt (hr i)
  let f := (projection ell r').toRingHom.comp (MvPolynomial.map φ)
  have hf : relationIdeal ell r ≤ RingHom.ker f := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change (projection ell r') ((X i ^ ell - r i).map φ) = 0
    rw [map_sub, map_pow, map_X, map_sub, map_pow, projection_X_pow]
    exact sub_self _
  let q : QuotientAlgebra ell r →+* QuotientAlgebra ell r' :=
    Ideal.Quotient.lift (relationIdeal ell r) f (fun _ hx => hf hx)
  have hproj (w : MvPolynomial (Fin n) S) :
      q (projection ell r w) = projection ell r' (w.map φ) := rfl
  let b := normalBasis hell r hr
  let b' := normalBasis hell r' hr'
  have hb (j : NormalIndex n ell) : q (b j) = b' j := by
    simp only [b, b', normalBasis_apply, normalClass, hproj, map_monomial, map_one]
  have hscalar (a : S) : q (algebraMap S (QuotientAlgebra ell r) a) =
      algebraMap T (QuotientAlgebra ell r') (φ a) := by
    rw [← (projection ell r).commutes a, ← (projection ell r').commutes (φ a),
      hproj, MvPolynomial.algebraMap_eq, MvPolynomial.algebraMap_eq, map_C]
  have hterm (a : S) (j : NormalIndex n ell) : q (a • b j) = φ a • b' j := by
    calc
      q (a • b j) = q (algebraMap S (QuotientAlgebra ell r) a * b j) :=
        congrArg q (Algebra.smul_def a (b j))
      _ = algebraMap T (QuotientAlgebra ell r') (φ a) * b' j := by
        rw [map_mul, hscalar, hb]
      _ = φ a • b' j := (Algebra.smul_def _ _).symm
  have hcoord (x : QuotientAlgebra ell r) (i : NormalIndex n ell) :
      φ (b.repr x i) = b'.repr (q x) i := by
    have hx := congrArg q (b.sum_repr x)
    rw [map_sum] at hx
    simp_rw [hterm] at hx
    rw [← hx, b'.repr_sum_self]
  ext i j
  change φ (Algebra.leftMulMatrix b (projection ell r v) i j) =
    Algebra.leftMulMatrix b' (projection ell r' (v.map φ)) i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    hcoord, map_mul, hproj, hb]

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

/-- Evaluating at a common zero of the normalized relations gives a root of the actual
multiplication matrix's characteristic polynomial, by Cayley–Hamilton in the quotient. -/
theorem isRoot_charpoly_multiplicationMatrix_of_aeval_eq (hell : 1 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree < ell)
    (v : MvPolynomial (Fin n) S) (x : Fin n → S) (hx : ∀ i, aeval x (r i) = x i ^ ell) :
    (multiplicationMatrix hell r hr v).charpoly.IsRoot (aeval x v) := by
  classical
  have hker : relationIdeal ell r ≤ RingHom.ker (aeval x).toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change aeval x (X i ^ ell - r i) = 0
    simp only [map_sub, map_pow, aeval_X, hx, sub_self]
  let ev := Ideal.Quotient.liftₐ (relationIdeal ell r) (aeval x) (fun _ h => hker h)
  have hev : ev (projection ell r v) = aeval x v :=
    congrArg (fun f : MvPolynomial (Fin n) S →ₐ[S] S => f v)
      (Ideal.Quotient.liftₐ_comp (relationIdeal ell r) (aeval x) (fun _ h => hker h))
  have hc : Polynomial.aeval (projection ell r v) (multiplicationMatrix hell r hr v).charpoly = 0 :=
    Algebra.aeval_charpoly_leftMulMatrix (normalBasis hell r hr) (projection ell r v)
  rw [Polynomial.IsRoot.def, ← Polynomial.coe_aeval_eq_eval, ← hev,
    Polynomial.aeval_algHom_apply, hc, map_zero]

end MvPolynomial.PurePower
