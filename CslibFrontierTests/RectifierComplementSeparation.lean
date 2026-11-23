/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Circuit.Rectifier.ComplementSeparation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Prime.Basic

/-!
# Client tests for rectifier (`OR`) circuits, Brown's matrix, and Sergeev's complement separation

Exercises the public module interface under ordinary imports. Domain checks ensure that
natural-valued `orComplexity` rejects an infinite row or column type, while extended-natural
`orDepthComplexity` remains available on those domains. Concrete finite examples cover:

1. **Disjoint-poles boundary (`idMatrix n`):** the `n × n` Boolean identity matrix is `2`-free of
   weight `n`, so `orComplexity (idMatrix n) = n` and `orDepthComplexity 1 (idMatrix n) = n`
   (which would collapse to `0` if input poles could coincide with output poles).
2. **Asymmetric orientation boundary (`asymMatrix`):** a `2 × 3` Boolean matrix checks
   row-versus-column indexing in `twoRectMatrix` and `complTwoRectCircuit`.
3. **Brown's `p = 3` (`27 × 27`) matrix:** verifies uniform row weight `6`, total weight `162`,
   `3`-rectangle-freeness (`isRectangleFreeMatrix_brownMatrix`), and tightness (`¬ 2`-free via an
   explicit `2 × 2` all-ones submatrix).
4. **Sergeev's `p = 3` (`351 × 351`) complement separation:** exercises Theorem 1(ii) on
   `sergeevComplementMatrix 3` (`OR_3 ≤ 2457`, `2`-free complement, and
   `351 ^ 4 ≤ 2 ^ 23 * OR(C̄) ^ 3`).
-/

set_option linter.privateModule false

namespace CslibFrontierTests.RectifierComplementSeparation

open Finset Cslib Cslib.Circuits

-- Neither infinite matrix dimension may collapse the natural-valued minimum to zero.
example : True := by
  fail_if_success
    have _ := orComplexity (fun (_ : ℕ) (_ : Fin 1) => false)
  fail_if_success
    have _ := orComplexity (fun (_ : Fin 1) (_ : ℕ) => false)
  trivial

-- The extended-natural API still represents infeasible infinite-domain problems by `⊤`.
example : orDepthComplexity 0 (fun (_ : ℕ) (_ : Fin 1) => true) = ⊤ :=
  orDepthComplexity_zero_eq_top (i := 0) (j := 0) rfl

/-- The `n × n` Boolean identity matrix. -/
private def idMatrix (n : ℕ) : Matrix (Fin n) (Fin n) Bool :=
  Matrix.of fun i j => decide (i = j)

private theorem isRectangleFreeMatrix_idMatrix (n : ℕ) : IsRectangleFreeMatrix (idMatrix n) 2 := by
  intro I J hI hJ hall
  obtain ⟨i₁, i₂, hi₁₂, rfl⟩ := card_eq_two.mp hI
  obtain ⟨j₁, _, _, rfl⟩ := card_eq_two.mp hJ
  have h1 : i₁ = j₁ := of_decide_eq_true (hall i₁ (by simp) j₁ (by simp))
  have h2 : i₂ = j₁ := of_decide_eq_true (hall i₂ (by simp) j₁ (by simp))
  exact hi₁₂ (h1.trans h2.symm)

private theorem boolMatrixWeight_idMatrix (n : ℕ) : boolMatrixWeight (idMatrix n) = n := by
  rw [boolMatrixWeight]
  have heq : (univ.filter fun p : Fin n × Fin n => idMatrix n p.1 p.2 = true) =
      (univ : Finset (Fin n)).image fun i => (i, i) := by
    ext ⟨i, j⟩
    simp only [idMatrix, Matrix.of_apply, decide_eq_true_eq, mem_filter, mem_univ, true_and,
      mem_image, Prod.mk.injEq]
    exact ⟨fun h => ⟨i, rfl, h⟩, fun ⟨k, hk1, hk2⟩ => hk1.symm.trans hk2⟩
  rw [heq, card_image_of_injective _ fun _ _ h => (Prod.mk.inj h).1, card_univ, Fintype.card_fin]

/-- Boundary check: `OR(I_n) = n` and `OR_1(I_n) = n` for all `n`. -/
example (n : ℕ) :
    orComplexity (idMatrix n) = n ∧ orDepthComplexity 1 (idMatrix n) = n := by
  refine ⟨?_, ?_⟩
  · rw [orComplexity_eq_boolMatrixWeight_of_isRectangleFree_two (isRectangleFreeMatrix_idMatrix n),
      boolMatrixWeight_idMatrix]
  · rw [orDepthComplexity_eq_boolMatrixWeight_of_isRectangleFree_two
        (isRectangleFreeMatrix_idMatrix n) le_rfl,
      boolMatrixWeight_idMatrix]

/-- Depth-`0` `⊤` boundary and direct `le_orComplexity` / `Walk.uncons` lower-bound check on
`idMatrix 1`. -/
example : orDepthComplexity 0 (idMatrix 1) = ⊤ ∧ 1 ≤ orComplexity (idMatrix 1) := by
  refine ⟨orDepthComplexity_zero_eq_top (i := 0) (j := 0) rfl, le_orComplexity fun _ C hC => ?_⟩
  obtain ⟨p⟩ := (hC 0 0).mp rfl
  obtain ⟨v, he, -⟩ := p.uncons (C.inp_ne_out 0 0)
  exact card_pos.mpr ⟨(C.inp 0, v), he⟩

/-- Asymmetric `2 × 3` matrix with row `0 = [true, true, false]` and row `1 = [true, true, true]`:
contains one `2 × 2` all-ones rectangle (`{0, 1} × {0, 1}`) and one `false` entry `(0, 2)`. -/
private def asymMatrix : Matrix (Fin 2) (Fin 3) Bool :=
  Matrix.of fun i j => !(i == 0 && j == 2)

example : boolMatrixWeight asymMatrix = 5 := by decide
example : boolMatrixWeight (twoRectMatrix asymMatrix) = 1 := by decide

/-- Asymmetric orientation witness for `complTwoRectCircuit`: `2 * C(3, 2) + 1 + 2 * C(2, 2) = 9`
edges, depth `≤ 3`, computing `(twoRectMatrix asymMatrix).map (! ·)`. -/
example :
    (complTwoRectCircuit asymMatrix).size = 9 ∧
    (complTwoRectCircuit asymMatrix).HasDepthLE 3 ∧
    (complTwoRectCircuit asymMatrix).Computes ((twoRectMatrix asymMatrix).map (! ·)) := by
  refine ⟨?_, hasDepthLE_three_complTwoRectCircuit asymMatrix,
    computes_complTwoRectCircuit asymMatrix⟩
  rw [size_complTwoRectCircuit]
  have hw : boolMatrixWeight (asymMatrix.map (! ·)) = 1 := by decide
  rw [hw, Fintype.card_fin, Fintype.card_fin]
  decide

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- Concrete check on `brownMatrix 3` (`27 × 27`): uniform row weight `6`, total weight `162`,
and `3`-rectangle-freeness. -/
example :
    (∀ x : Fin 3 → ZMod 3,
      #(univ.filter fun y => brownMatrix 3 x y = true) = 6) ∧
    boolMatrixWeight (brownMatrix 3) = 162 ∧
    IsRectangleFreeMatrix (brownMatrix 3) 3 :=
  ⟨fun x => card_row_brownMatrix rfl x,
    boolMatrixWeight_brownMatrix (p := 3) rfl,
    isRectangleFreeMatrix_brownMatrix (p := 3) rfl⟩

/-- Tightness witness: `brownMatrix 3` is not `2`-rectangle-free, witnessed by the `2 × 2` unit
square `{(0, 0, 0), (1, 1, 0)} × {(1, 0, 0), (0, 1, 0)}` in `(ℤ/3ℤ)^3`. -/
example : ¬ IsRectangleFreeMatrix (brownMatrix 3) 2 := by
  intro h2
  let a₀ : Fin 3 → ZMod 3 := ![0, 0, 0]
  let a₁ : Fin 3 → ZMod 3 := ![1, 1, 0]
  let b₀ : Fin 3 → ZMod 3 := ![1, 0, 0]
  let b₁ : Fin 3 → ZMod 3 := ![0, 1, 0]
  have ha : a₀ ≠ a₁ := fun h => by simpa [a₀, a₁] using congrFun h 0
  have hb : b₀ ≠ b₁ := fun h => by simpa [b₀, b₁] using congrFun h 0
  refine h2 {a₀, a₁} {b₀, b₁} (card_pair ha) (card_pair hb) fun i hi j hj => ?_
  rcases mem_insert.mp hi with rfl | hi'
  · rcases mem_insert.mp hj with rfl | hj'
    · decide
    · rw [mem_singleton.mp hj']; decide
  · rw [mem_singleton.mp hi']
    rcases mem_insert.mp hj with rfl | hj'
    · decide
    · rw [mem_singleton.mp hj']; decide

/-- Concrete instantiation of Sergeev's Theorem 1(ii) at `p = 3` (`n = C(27, 2) = 351`). -/
example :
    orDepthComplexity 3 (sergeevComplementMatrix 3) ≤ (2457 : ℕ) ∧
    orComplexity (sergeevComplementMatrix 3) ≤ 2457 ∧
    IsRectangleFreeMatrix ((sergeevComplementMatrix 3).map (! ·)) 2 ∧
    351 ^ 4 ≤ 2 ^ 23 * orComplexity ((sergeevComplementMatrix 3).map (! ·)) ^ 3 :=
  ⟨orDepthComplexity_three_sergeevComplementMatrix_le (p := 3) rfl,
    orComplexity_sergeevComplementMatrix_le (p := 3) rfl,
    isRectangleFreeMatrix_compl_sergeevComplementMatrix (p := 3) rfl,
    choose_pow_four_le_mul_orComplexity_compl_sergeevComplementMatrix_pow_three (p := 3) rfl⟩

end CslibFrontierTests.RectifierComplementSeparation
