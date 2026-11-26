/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module

public import CslibFrontier.Computability.Circuit.Boolean.CycleMinor
public import Mathlib.Data.ZMod.Basic

/-! Concrete `module` clients for the cycle-and-minor function at `d = 4`: the two branches, the
multilinear representatives, concrete values of both branches, and the identities used for the
lower bounds. -/

public section

namespace CslibFrontierTests.CycleMinor

open Cslib.Circuits MvPolynomial Cslib.BitString

/-- The function is the cycle test for `b = 0` and the minor bit for `b = 1`. -/
example (x : Fin 4 → Bool) (Y : Fin 4 × Fin 4 → Bool) :
    cycleMinor false x Y = (open Classical in decide (IsCycleMatrix Y)) ∧
      cycleMinor true x Y = minorBit x Y := by
  simp

/-- The matrix of the `4`-cycle `0 → 1 → 2 → 3 → 0` is a cycle matrix. -/
example : IsCycleMatrix (CycleMinor.permBoolMatrix (finRotate 4)) := by
  rw [isCycleMatrix_permBoolMatrix_iff]
  have h : ∀ x y : Fin 4, (finRotate 4).SameCycle x y := by decide
  exact ⟨Set.bijOn_univ.mpr (finRotate 4).bijective, fun x _ y _ => h x y⟩

/-- The matrix of the product `(0 1)(2 3)` of two disjoint transpositions is not a cycle matrix. -/
example : ¬IsCycleMatrix (CycleMinor.permBoolMatrix
    (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3)) := by
  rw [isCycleMatrix_permBoolMatrix_iff]
  exact fun h => absurd (h.2 (Set.mem_univ 0) (Set.mem_univ 2)) (by decide)

/-- The minor bit is `0` when `x` selects three columns instead of two. -/
example (Y : Fin 4 × Fin 4 → Bool) : minorBit ![true, true, true, false] Y = false :=
  minorBit_of_card_ne Y (by decide)

/-- The minor on the first two columns of a matrix whose first two rows are `[1, 0, *, *]` and
`[1, 1, *, *]` is nonsingular over `F₂`. -/
example : minorBit ![true, true, false, false]
    (fun v => decide (v.2 ≤ v.1)) = true := by
  rw [minorBit_eq_det _ (Fin.castLEOrderEmb (by norm_num)) (by decide) (by decide)]
  simp [Matrix.det_fin_two, bitVal]

/-- The minor on the first two columns of a matrix whose first two rows are both `[1, 1, *, *]` is
singular over `F₂`. -/
example : minorBit ![true, true, false, false] (fun _ => true) = false := by
  rw [minorBit_eq_det _ (Fin.castLEOrderEmb (by norm_num)) (by decide) (by decide)]
  simp [Matrix.det_fin_two, bitVal]

/-- The component of degree `4` of the cycle branch is the Hamiltonian cycle sum. -/
example : homogeneousComponent 4 (cyclePoly (d := 4) ℤ) =
    (Matrix.of fun i j => (X (i, j) : MvPolynomial (Fin 4 × Fin 4) ℤ)).hamiltonianCycleSum :=
  homogeneousComponent_cyclePoly

/-- Over `F₂` the generic minor is multilinear and is the minor bit on the Boolean matrices. -/
example (x : Fin 4 → Bool) (Y : Fin 4 × Fin 4 → Bool) :
    minorPoly (ZMod 2) x ∈ restrictDegree (Fin 4 × Fin 4) (ZMod 2) 1 ∧
      eval (bitPoint Y) (minorPoly (ZMod 2) x) = bitVal (ZMod 2) (minorBit x Y) :=
  ⟨minorPoly_mem_restrictDegree x, eval_bitPoint_minorPoly x Y⟩

/-- At a padded `2 × 4` matrix the generic minor is the minor of the matrix at the columns
of `x`. -/
example (C : Matrix (Fin (4 / 2)) (Fin 4) ℤ) (x : Fin 4 → Bool) :
    eval (CycleMinor.padRows C) (minorPoly ℤ x) = if h : (CycleMinor.selected x).card = 4 / 2 then
      (C.submatrix id ((CycleMinor.selected x).orderEmbOfFin h)).det else 0 :=
  eval_padRows_minorPoly C x

end CslibFrontierTests.CycleMinor
