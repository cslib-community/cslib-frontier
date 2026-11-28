/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate
public import CslibFrontier.Computability.Circuit.Boolean.Lupanov.FormulaSynthesis

/-!
# Clients of Lupanov's formula synthesis

The selectors distinguish a sphere's center, one-bit neighbors and two-bit flips. Finite synthesis
is exercised across both variable blocks, including a row block larger than the entire row set.
The source-model bridge also handles constant functions, although native constants have no leaves.
-/

public section

namespace CslibFrontierTests.LupanovFormula

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.LupanovFormula

private def center : BitString 4 := fun _ => false

-- An open sphere excludes its center and any point at distance two.
example : (Formula.openSphere center).eval interpretation center = false := by
  rw [Formula.eval_openSphere]
  decide

example : (Formula.openSphere center).eval interpretation
    (BitString.flipOn {0, 1} center) = false := by
  rw [Formula.eval_openSphere]
  decide

example : (Formula.openSphere center).eval interpretation
    (BitString.flipOn {3} center) = true := by
  simp only [Formula.eval_openSphere, decide_eq_true_eq]
  exact ⟨3, rfl⟩

-- A two-literal selector chooses two of the four neighbors, not the whole sphere.
example : (Formula.neighborSelector center {0, 2}).leafSize = 2 := by simp

example : (Formula.neighborSelector center {0, 2}).eval interpretation
    (BitString.flipOn {0} center) = true := by simp [Formula.eval_neighborSelector_flip]

example : (Formula.neighborSelector center {0, 2}).eval interpretation
    (BitString.flipOn {1} center) = false := by simp [Formula.eval_neighborSelector_flip]

-- The r = 0 partition still has two centers and covers both one-bit assignments exactly once.
example : ∃ C : Finset (BitString 1), C.card = 2 ∧
    Function.Bijective (fun p : {c // c ∈ C} × Fin 1 => BitString.flipOn {p.2} p.1.val) := by
  simpa using BitString.exists_openSpherePartition 0

private def acrossBlocks (x : BitString 7) : Bool := x 0 ^^ x 6

-- Eight rows split into blocks of two; the function couples a row input and a sphere input.
example : ∃ F : Formula signature 7, F.IsConstantFree ∧ F.IsNNF ∧
    F.Computes interpretation acrossBlocks ∧ F.leafSize ≤ 624 ∧
    F.eval interpretation (fun _ => false) = false ∧
    F.eval interpretation (fun i => decide (i = 6)) = true := by
  obtain ⟨F, hF, hNNF, hf, hsize⟩ :=
    exists_constantFree_isNNF_leafSize_le_formulaBound 0 3 2 2 (by decide) acrossBlocks
  refine ⟨F, hF, hNNF, hf, ?_, ?_, ?_⟩
  · simpa [formulaBound] using hsize
  · rw [hf]
    rfl
  · rw [hf]
    rfl

-- A block capacity exceeding the two available rows leaves only one nonempty row block.
example : ∃ F : Formula signature 3, F.IsConstantFree ∧ F.IsNNF ∧
    F.Computes interpretation (fun x => x 0 && !x 2) ∧ F.leafSize ≤ 60 := by
  simpa [formulaBound] using
    exists_constantFree_isNNF_leafSize_le_formulaBound 0 1 1 3 (by decide)
      (fun x => x 0 && !x 2)

-- Constant propagation and normalization preserve an internal negation after deleting constants.
private def withConstants : Formula signature 2 :=
  ((Formula.const false).or ((Formula.input 0).and (Formula.const true))).not

example : ∃ F : Formula signature 2, F.IsConstantFree ∧ F.IsNNF ∧
    F.Computes interpretation (fun x => !x 0) ∧ F.leafSize ≤ 2 := by
  obtain ⟨F, hF, hNNF, heval, hsize⟩ :=
    Formula.exists_constantFree_isNNF_leafSize_le (by decide) withConstants
  refine ⟨F, hF, hNNF, fun x => ?_, ?_⟩
  · simpa [withConstants] using heval x
  · simpa [withConstants] using hsize

/-- A native zero-leaf constant becomes a literal-only formula of at most two leaves. -/
theorem constant_true_constantFree_nnf : ∃ F : Formula signature 1, F.IsConstantFree ∧ F.IsNNF ∧
    F.Computes interpretation (fun _ => true) ∧ F.leafSize ≤ 2 := by
  simpa [Formula.Computes] using Formula.exists_constantFree_isNNF_leafSize_le (by decide)
    (Formula.const true : Formula signature 1)

example : ¬ (Formula.const true : Formula signature 0).IsConstantFree := by
  simp [Formula.IsConstantFree, Formula.const]

end CslibFrontierTests.LupanovFormula
