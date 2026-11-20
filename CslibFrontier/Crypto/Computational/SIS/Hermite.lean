/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SIS.Module
import Mathlib.Algebra.BigOperators.Fin

/-!
# Hermite normal form Module-SIS

The MSIS experiment in [Bai et al., §6.1][BaiEtAl2021Dilithium] samples a uniform matrix
`A` and asks for a short nonzero integer vector in the kernel of `[I | A]`. The identity
block consists of constant polynomials. This representation uses the same integer solution
predicate as the full-matrix Module-SIS experiment.
-/

public section

namespace Cslib.Crypto.ModuleSIS

variable {d k n q : ℕ}

/-- The challenge matrix `[I | A]` of Hermite normal form Module-SIS. -/
def hermiteMatrix (A : Matrix (Fin d) (Fin k) (Fin n → ZMod q)) :
    Matrix (Fin d) (Fin (d + k)) (Fin n → ZMod q) :=
  fun i => Fin.append (fun j => if j = i then (1 : Negacyclic (ZMod q) n).coeffs else 0) (A i)

/-- The two blocks act by `(u,z) ↦ u + A z` in the negacyclic ring. -/
theorem moduleSISMap_hermiteMatrix (A : Matrix (Fin d) (Fin k) (Fin n → ZMod q))
    (u : Fin d → Fin n → ZMod q) (z : Fin k → Fin n → ZMod q) :
    moduleSISMap (hermiteMatrix A) (Fin.append u z) = u + moduleSISMap A z := by
  funext i
  simp only [moduleSISMap, hermiteMatrix, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
    Pi.add_apply, add_left_inj]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

/-- The fixed-parameter experiment of §6.1. Sample the right block uniformly and test the
solver's integer vector against the full matrix `[I | A]`. -/
@[expose] noncomputable def hermiteExperiment [NeZero q] (β : ℕ)
    (solver : Matrix (Fin d) (Fin k) (Fin n → ZMod q) → ProbComp (Fin (d + k) → Fin n → ℤ)) :
    ProbComp Bool := do
  let A ← ProbComp.uniform (Matrix (Fin d) (Fin k) (Fin n → ZMod q))
  let y ← solver A
  return decide (IsSolution (hermiteMatrix A) β y)

end Cslib.Crypto.ModuleSIS
