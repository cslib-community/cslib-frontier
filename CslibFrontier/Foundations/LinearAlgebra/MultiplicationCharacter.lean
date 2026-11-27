/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, multiplication eigenvalues)

public import CslibFrontier.Init
public import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Zero

/-!
# An algebra homomorphism from a simple multiplication eigenvalue

Multiplication preserves the eigenspace of a multiplication operator in a commutative
algebra. At a simple characteristic root, that eigenspace is a line, and the scalar action
on it determines an algebra homomorphism to the base field.

Adapted from `SimpleEigenvalueCharacter` and `CharacterOfEigenline` in lean-canny at
`970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace Algebra

open Module

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A] [Module.Finite K A]

/-- A simple characteristic root of multiplication by `v` is the image of `v` under
an algebra homomorphism to the base field. -/
theorem exists_algHom_of_rootMultiplicity_lmul_eq_one (v : A) {η : K}
    (hsimple : (Algebra.lmul K A v).charpoly.rootMultiplicity η = 1) :
    ∃ χ : A →ₐ[K] K, χ v = η := by
  let φ := Algebra.lmul K A v
  have hroot : φ.charpoly.IsRoot η :=
    (Polynomial.rootMultiplicity_pos (LinearMap.charpoly_monic φ).ne_zero).mp
      (hsimple.symm ▸ Nat.zero_lt_one)
  have heigen := (Module.End.hasEigenvalue_iff_isRoot_charpoly φ η).mpr hroot
  obtain ⟨w, hw⟩ := heigen.exists_hasEigenvector
  have hvw : v * w = η • w := by
    simpa only [φ, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply'] using hw.apply_eq_smul
  let w' : φ.eigenspace η := ⟨w, hw.1⟩
  have hw' : w' ≠ 0 := fun h => hw.2 (congrArg Subtype.val h)
  have hupper := LinearMap.finrank_eigenspace_le φ η
  have hpos : 0 < finrank K (φ.eigenspace η) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨w', hw'⟩
  have hdim : finrank K (φ.eigenspace η) = 1 := by
    change φ.charpoly.rootMultiplicity η = 1 at hsimple
    omega
  have hline (a : A) : ∃ c : K, c • w = a * w := by
    have ha : a * w ∈ φ.eigenspace η := by
      apply Module.End.mem_eigenspace_iff.mpr
      change v * (a * w) = η • (a * w)
      rw [mul_left_comm v a w, hvw, mul_smul_comm]
    obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hdim hw' ⟨a * w, ha⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  choose c hc using hline
  have hinj : Function.Injective (fun t : K => t • w) := smul_left_injective K hw.2
  refine ⟨{ toFun := c
            map_zero' := hinj (by simpa only [zero_smul, zero_mul] using hc 0)
            map_one' := hinj (by simpa only [one_smul, one_mul] using hc 1)
            map_mul' := ?_
            map_add' := ?_
            commutes' := ?_ }, hinj ((hc v).trans hvw)⟩
  · intro a b
    apply hinj
    change c (a * b) • w = (c a * c b) • w
    rw [hc, mul_assoc, ← hc b, mul_smul_comm, ← hc a, smul_smul, mul_comm (c b)]
  · intro a b
    apply hinj
    change c (a + b) • w = (c a + c b) • w
    rw [hc, add_smul, hc, hc, add_mul]
  · intro t
    apply hinj
    change c (algebraMap K A t) • w = t • w
    rw [hc, Algebra.smul_def]

end Algebra
