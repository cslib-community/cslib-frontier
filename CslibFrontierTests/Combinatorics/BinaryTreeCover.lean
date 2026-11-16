/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Foundations.Combinatorics.BinaryTreeCover

/-! Tests and hypothesis-necessity probes for `Cslib.CompleteBinaryTree.cover`. -/

public section

namespace CslibFrontierTests.Combinatorics.BinaryTreeCover

open Cslib.CompleteBinaryTree

/-! Worked example from Boneh–Shoup Fig. 5.6 (p. 208; p. 206 describes the example): `n = 8`,
`S = {1, 2, 4, 5, 6}` (0-indexed `{0, 1, 3, 4, 5}`), `r = 3` revoked leaves `{2, 6, 7}`. Also
verifies minimality against the all-leaves cover of size `5`. -/

example :
    let S : Finset (Fin (2 ^ 3)) := {0, 1, 3, 4, 5}
    let Wleaves : Finset (Node 3) :=
      S.image fun i => ⟨0, i.1, Nat.zero_le 3, by simp⟩
    (cover S).card = 3 ∧ Covers (cover S) S ∧ Covers Wleaves S ∧
      (cover S).card ≤ Wleaves.card ∧
      ((cover S).card : ℝ) ≤ (3 : ℝ) * Real.logb 2 ((2 ^ 3 : ℝ) / 3) := by
  intro S Wleaves
  have hcovW : Covers Wleaves S := by
    intro i
    simp [Wleaves, Node.CoversLeaf, Fin.val_inj]
  refine ⟨by decide, covers_cover S, hcovW, card_cover_le_of_covers hcovW, ?_⟩
  simpa using card_cover_le (r := 3) (S := S) (by decide) (by decide)

/-! Base case `n = 1` (`h = 0`, `r = 1`): `S = ∅` gives `|cover(∅)| = 0 ≤ 1 * log₂(1 / 1) = 0`. -/

example :
    let S : Finset (Fin (2 ^ 0)) := ∅
    (cover S).card = 0 ∧ Covers (cover S) S ∧
      ((cover S).card : ℝ) ≤ (1 : ℝ) * Real.logb 2 ((2 ^ 0 : ℝ) / 1) := by
  intro S
  refine ⟨by decide, covers_cover S, ?_⟩
  simpa using card_cover_le (r := 1) (S := S) (by decide) (by decide)

/-! Boundary `r₁ = 0` case (where the book omits `+ 1`): `n = 4`, `S = {0, 1, 2}`, `r = 1`. -/

example :
    let S : Finset (Fin (2 ^ 2)) := {0, 1, 2}
    (cover S).card = 2 ∧
      ((cover S).card : ℝ) ≤ (1 : ℝ) * Real.logb 2 ((2 ^ 2 : ℝ) / 1) := by
  intro S
  refine ⟨by decide, ?_⟩
  simpa using card_cover_le (r := 1) (S := S) (by decide) (by decide)

/-! Necessity of `1 ≤ r`: for `r = 0` (`S = univ`), `|cover(S)| = 1 > 0 = 0 * log₂(n / 0)`. -/

example (h : ℕ) :
    ¬ (((cover (Finset.univ : Finset (Fin (2 ^ h)))).card : ℝ) ≤
        (0 : ℝ) * Real.logb 2 ((2 ^ h : ℝ) / (0 : ℕ))) := by
  simp [cover_univ]

/-! `S.card + r = 2 ^ h` cannot be weakened to `2 ^ h ≤ S.card + r`, nor replaced by the truncated
subtraction `S.card = 2 ^ h - r`: for `h = 0`, `r = 2`, `S = ∅` satisfies both, yet
`|cover(∅)| = 0 > 2 * log₂(1 / 2) = -2`. -/

example :
    let S : Finset (Fin (2 ^ 0)) := ∅
    S.card = 2 ^ 0 - 2 ∧ 2 ^ 0 ≤ S.card + 2 ∧
      ¬ (((cover S).card : ℝ) ≤ (2 : ℝ) * Real.logb 2 ((2 ^ 0 : ℝ) / 2)) := by
  intro S
  refine ⟨rfl, by decide, ?_⟩
  simp [S, cover]

/-! `S.card + r = 2 ^ h` cannot be weakened to `S.card + r ≤ 2 ^ h`: for `h = 3` (`n = 8`) and
`S = {0, 2, 4, 6}`, taking `r = 1` gives `|cover(S)| = 4 > 3 = 1 * log₂(8 / 1)`. -/

example :
    let S : Finset (Fin (2 ^ 3)) := {0, 2, 4, 6}
    S.card + 1 ≤ 2 ^ 3 ∧
      ¬ (((cover S).card : ℝ) ≤ (1 : ℝ) * Real.logb 2 ((2 ^ 3 : ℝ) / 1)) := by
  intro S
  have h4 : (cover S).card = 4 := by decide
  refine ⟨by decide, ?_⟩
  rw [h4, div_one, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
  norm_num

end CslibFrontierTests.Combinatorics.BinaryTreeCover

end
