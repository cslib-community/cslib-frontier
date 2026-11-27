/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate (Mathlib, pure-power polynomial residues and traces)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.Basis
public import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.Kernel
public import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.Jacobian
public import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.Specialization
public import CslibFrontier.Foundations.RingTheory.Trace.Reproducing

/-!
# Multiplication traces as finite pure-power residues

For the actual quotient by `X i ^ (d + 1) - r i`, where `d ≥ 1` and each lower part has
total degree at most `d`, `trace_eq_residue` computes the trace of multiplication by `v` as
the finite residue of `v` times the Jacobian polynomial. The construction uses the proved
normal-monomial basis and the normalized polynomial reproducing kernel, rather than assuming
either a quotient model or a trace formula. The coefficient ring is an arbitrary commutative
ring; multiple roots and nilpotents are allowed.

This is an algebraic step toward real-arithmetic counting bounds, ported from
`LeanCanny.CountingHierarchy.PurePowerTrace` at lean-canny commit
`970f28a5ecefc1327402ade16c068aa4b1b2c183`. No complexity bound is asserted here.
-/

public section

namespace MvPolynomial.PurePower

open Module
open scoped BigOperators

variable {S : Type*} [CommRing S] {n : ℕ}

/-- In a pure-power quotient, multiplication trace is the finite residue against the Jacobian.
The degree hypotheses ensure a finite normal-monomial basis; simple roots are not required. -/
theorem trace_eq_residue (d : ℕ) (hd : 1 ≤ d)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree ≤ d)
    (v : MvPolynomial (Fin n) S) :
    Algebra.trace S (QuotientAlgebra (d + 1) r) (projection (d + 1) r v) =
      residue (d + 1) r (v * jacobian (d + 1) r) := by
  let A := QuotientAlgebra (d + 1) r
  let φ : S →+* A := algebraMap S A
  let π := projection (d + 1) r
  let x : Fin n → A := fun i => π (X i)
  let r' : Fin n → MvPolynomial (Fin n) A := fun i => (r i).map φ
  have hell : 1 ≤ d + 1 := by omega
  have hrS (i : Fin n) : (r i).totalDegree < d + 1 := (hr i).trans_lt (Nat.lt_succ_self d)
  have hrA (i : Fin n) : (r' i).totalDegree ≤ d := (totalDegree_map_le φ (r i)).trans (hr i)
  have heval (q : MvPolynomial (Fin n) S) : eval x (q.map φ) = π q := by
    rw [eval_map]
    exact congrArg (fun f : MvPolynomial (Fin n) S →ₐ[S] A => f q) (aeval_unique π).symm
  obtain ⟨K, hk, hdiag⟩ := purePower_reproducing_kernel x d hd r' hrA
    fun i => (heval _).trans (projection_X_pow (d + 1) r i).symm
  let L := quotientFunctional hell r hrS
  let m : (Fin n →₀ ℕ) → A := fun e => π (monomial e 1)
  let c : (Fin n →₀ ℕ) → A := fun e => K.coeff e
  have hrep (z : A) : ∑ e ∈ K.support, L (m e * z) • c e = z := by
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective z
    change (∑ e ∈ K.support, L (m e * π q) • c e) = π q
    have hsum := (residue_kernel_expansion φ hell r hrS K q).symm.trans (hk (q.map φ))
    rw [heval] at hsum
    refine (Finset.sum_congr rfl fun e _ => ?_).trans hsum
    change quotientFunctional hell r hrS
      (projection (d + 1) r (monomial e 1) * projection (d + 1) r q) • K.coeff e = _
    rw [← map_mul, quotientFunctional_projection]
    exact (Algebra.smul_def (residue (d + 1) r (monomial e 1 * q)) (K.coeff e)).trans (mul_comm _ _)
  have hJac : Matrix.det (Matrix.of (fun i j => eval x (pderiv j (X i ^ (d + 1) - r' i)))) =
      π (jacobian (d + 1) r) := calc
    _ = eval x (jacobian (d + 1) r') :=
      ((eval x).map_det (Matrix.of fun i j => pderiv j (X i ^ (d + 1) - r' i))).symm
    _ = _ := by rw [← jacobian_map φ (d + 1) r, heval]
  have heuler : (∑ e ∈ K.support, c e * m e) = π (jacobian (d + 1) r) := by
    calc
      _ = eval x K := by
        conv_rhs => rw [K.as_sum]
        rw [map_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        simp [c, m, ← heval, eval_monomial]
      _ = _ := hdiag.trans hJac
  let b : Basis (NormalIndex n (d + 1)) S A := normalBasis hell r hrS
  let : Module.Free S A := Module.Free.of_basis b
  let : Module.Finite S A := Module.Finite.of_basis b
  calc
    _ = L (π v * ∑ e ∈ K.support, c e * m e) :=
      Algebra.trace_eq_of_reproducing L K.support c m hrep (π v)
    _ = _ := by rw [heuler, ← map_mul, quotientFunctional_projection]

end MvPolynomial.PurePower
