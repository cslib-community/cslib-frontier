/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Formula
import Mathlib.Tactic.Linarith

/-!
# Correcting overlapping approximate counts

This module proves the arithmetic correction step in the proof of Lemma 1 of
[Sergeev2025Symmetric], §3, pp. 12–13, and correctness of an explicit sequential reconstruction
from independently rounded high parts. Each supplied approximation is either the true high part
or its successor. Comparing two overlap bits determines whether to borrow from the previous
high part or replace the new low block by the largest digit.

The arithmetic is stated for any positive radix; the paper uses radix `2 ^ s`, with `s ≥ 2`.
The reconstruction computes from the supplied approximations alone: it does not inspect the true
value appearing in the correctness theorem. These are steps toward the paper's approximate
counting construction, not its parallel per-block depth bound. The remaining construction and
depth estimates are tracked in issue #7708.

## Main definitions

* `Cslib.Circuits.Boolean.ApproximateCount.correctBlock`: the overlap correction rule.
* `Cslib.Circuits.Boolean.ApproximateCount.reconstruct`: sequential reconstruction from rounded
  high parts, most significant first.
* `Cslib.Circuits.Boolean.ApproximateCount.borrowFormula`: a constant-size De Morgan formula for
  the correction bit, with the low two bits of each overlap as inputs.

## Main results

* `Cslib.Circuits.Boolean.ApproximateCount.extend_correctBlock_of_rounding`: one correction step
  preserves the one-sided error of at most one.
* `Cslib.Circuits.Boolean.ApproximateCount.reconstruct_of_rounding`: the same invariant for any
  number of blocks, with outputs tied to the supplied approximations.
* `Cslib.Circuits.Boolean.ApproximateCount.eval_borrowFormula_overlap`: the native formula computes
  exactly the correction bit chosen by `correctBlock`.

## References

* [I. S. Sergeev, *Economical formulae for symmetric boolean functions*, preprint 1 May 2025,
  §3, proof of Lemma 1, equation (4), pp. 12–13][Sergeev2025Symmetric]
-/

public section

namespace Cslib.Circuits.Boolean.ApproximateCount

/-- One low radix digit and a borrow to apply to the already reconstructed high part. -/
structure Block where
  /-- The low digit to append. -/
  digit : ℕ
  /-- Whether the high part must first be decreased by one. -/
  borrow : Bool
  deriving DecidableEq, Repr

/-- Append a corrected low digit to a high part, using natural subtraction for the borrow. -/
@[expose] def Block.extend (block : Block) (radix high : ℕ) : ℕ :=
  (high - block.borrow.toNat) * radix + block.digit

/-- The arithmetic rule in Sergeev's proof of Lemma 1: compare the residues modulo four of
`high` and `estimate / radix`. Borrow when the former is one ahead; replace the low digit by
`radix - 1` when the latter is one ahead. -/
@[expose] def correctBlock (radix high estimate : ℕ) : Block where
  digit := if estimate / radix % 4 = (high + 1) % 4 then radix - 1 else estimate % radix
  borrow := decide (high % 4 = (estimate / radix + 1) % 4)

/-- A native De Morgan formula testing whether the two-bit word `(a₁,a₀)` is the successor
modulo four of `(b₁,b₀)`. It computes the borrow bit of the overlap correction. -/
@[expose] def borrowFormula {n : ℕ} (a₀ a₁ b₀ b₁ : Fin n) : Formula signature n :=
  ((Formula.input a₀).xor (.input b₀)).and
    (((Formula.input a₁).xor ((Formula.input b₁).xor (.input b₀))).not)

/-- Boolean semantics of the overlap comparison. The word order is low bit first. -/
@[simp] theorem eval_borrowFormula {n : ℕ} (a₀ a₁ b₀ b₁ : Fin n) (x : BitString n) :
    (borrowFormula a₀ a₁ b₀ b₁).eval interpretation x =
      decide ((x a₀).toNat + 2 * (x a₁).toNat =
        ((x b₀).toNat + 2 * (x b₁).toNat + 1) % 4) := by
  simp only [borrowFormula, Formula.eval_and, Formula.eval_xor, Formula.eval_not,
    Formula.eval_input]
  cases x a₀ <;> cases x a₁ <;> cases x b₀ <;> cases x b₁ <;> rfl

/-- The correction-bit formula has twenty-two De Morgan operation nodes. -/
@[simp] theorem size_borrowFormula {n : ℕ} (a₀ a₁ b₀ b₁ : Fin n) :
    (borrowFormula a₀ a₁ b₀ b₁).size = 22 := by
  simp [borrowFormula]

/-- The correction-bit formula has depth at most eight, independently of the block width. -/
theorem depth_borrowFormula_le {n : ℕ} (a₀ a₁ b₀ b₁ : Fin n) :
    (borrowFormula a₀ a₁ b₀ b₁).depth ≤ 8 := by
  simp [borrowFormula, Formula.xor]

/-- Feeding the actual two-bit overlaps to the native formula computes the borrow selected by
`correctBlock`; this links the Boolean realization to the arithmetic correction. -/
theorem eval_borrowFormula_overlap (radix high estimate : ℕ) :
    (borrowFormula (0 : Fin 4) 1 2 3).eval interpretation
      ![high.testBit 0, high.testBit 1, (estimate / radix).testBit 0,
        (estimate / radix).testBit 1] = (correctBlock radix high estimate).borrow := by
  rw [eval_borrowFormula]
  change decide ((high.testBit 0).toNat + 2 * (high.testBit 1).toNat =
    (((estimate / radix).testBit 0).toNat + 2 * ((estimate / radix).testBit 1).toNat + 1) % 4) = _
  simp only [Nat.toNat_testBit, pow_zero, pow_one, Nat.div_one, correctBlock]
  exact decide_eq_decide.mpr (by omega)

/-- The corrected low digit is a radix digit, even without the approximation invariant. -/
theorem digit_correctBlock_lt {radix : ℕ} (hr : 0 < radix) (high estimate : ℕ) :
    (correctBlock radix high estimate).digit < radix := by
  simp only [correctBlock]
  split
  · omega
  · exact Nat.mod_lt _ hr

private theorem extend_correctBlock_same (radix high estimate : ℕ)
    (h : estimate / radix = high) :
    (correctBlock radix high estimate).extend radix high = estimate := by
  have h₁ : ¬ high % 4 = (estimate / radix + 1) % 4 := by omega
  have h₂ : ¬ estimate / radix % 4 = (high + 1) % 4 := by omega
  simp only [Block.extend, correctBlock, h₁, h₂, ↓reduceIte, decide_false,
    Bool.toNat_false, Nat.sub_zero]
  simpa only [h, Nat.mul_comm] using Nat.div_add_mod estimate radix

private theorem extend_correctBlock_ahead (radix high estimate : ℕ)
    (h : high = estimate / radix + 1) :
    (correctBlock radix high estimate).extend radix high = estimate := by
  have h₁ : high % 4 = (estimate / radix + 1) % 4 := by omega
  have h₂ : ¬ estimate / radix % 4 = (high + 1) % 4 := by omega
  simp only [Block.extend, correctBlock, h₁, h₂, ↓reduceIte, decide_true, Bool.toNat_true]
  simpa only [h, Nat.add_sub_cancel, Nat.mul_comm] using Nat.div_add_mod estimate radix

/-- An arithmetic step in Sergeev's approximate-count construction, not its depth bound.
If `high` approximates `value / radix` and `estimate` approximates `value`, both by rounding
up by at most one, the explicitly corrected extension still equals `value` or `value + 1`.
No approximation or correction is selected by the conclusion. -/
theorem extend_correctBlock_of_rounding {radix value high estimate : ℕ} (hr : 0 < radix)
    (hhigh : high = value / radix ∨ high = value / radix + 1)
    (hestimate : estimate = value ∨ estimate = value + 1) :
    (correctBlock radix high estimate).extend radix high = value ∨
      (correctBlock radix high estimate).extend radix high = value + 1 := by
  rcases hestimate with rfl | rfl
  · rcases hhigh with rfl | rfl
    · exact Or.inl (extend_correctBlock_same _ _ _ rfl)
    · exact Or.inl (extend_correctBlock_ahead _ _ _ rfl)
  · have hbound : value + 1 ≤ radix * (value / radix + 1) := by
      nlinarith [Nat.mod_lt value hr, Nat.div_add_mod value radix]
    have hquot : (value + 1) / radix = value / radix ∨
        (value + 1) / radix = value / radix + 1 := by
      have := Nat.div_le_div_right (by omega : value ≤ value + 1) (c := radix)
      have := Nat.div_le_of_le_mul hbound
      omega
    rcases hquot with hquot | hquot
    · rcases hhigh with rfl | rfl
      · exact Or.inr (extend_correctBlock_same _ _ _ hquot)
      · exact Or.inr (extend_correctBlock_ahead _ _ _ (by omega))
    · rcases hhigh with rfl | rfl
      · have hcarry : value + 1 = (value / radix + 1) * radix := le_antisymm
          (Nat.mul_comm _ _ ▸ hbound) (hquot ▸ Nat.div_mul_le_self (value + 1) radix)
        have h₁ : ¬ value / radix % 4 = ((value + 1) / radix + 1) % 4 := by omega
        have h₂ : (value + 1) / radix % 4 = (value / radix + 1) % 4 := by rw [hquot]
        left
        simp only [correctBlock, Block.extend, h₂, ↓reduceIte, h₁, decide_false,
          Bool.toNat_false, Nat.sub_zero]
        simp only [Nat.add_mul, Nat.one_mul] at hcarry
        omega
      · exact Or.inr (extend_correctBlock_same _ _ _ hquot)

/-- Reconstruct the low value from `levels + 1` rounded high-part estimates. `estimate i`
approximates the value divided by `radix ^ i`; the highest estimate initializes the recursion.
The algorithm has no access to the true value. -/
@[expose] def reconstruct (radix : ℕ) : ℕ → (ℕ → ℕ) → ℕ
  | 0, estimate => estimate 0
  | levels + 1, estimate =>
      let high := reconstruct radix levels (fun i => estimate (i + 1))
      (correctBlock radix high (estimate 0)).extend radix high

/-- Sequential correctness of the block reconstruction, an arithmetic step toward Sergeev's
Lemma 1. This does not assert that the sequential reconstruction has the paper's parallel depth.
Every approximation used by the algorithm is constrained, including the initial high part. -/
theorem reconstruct_of_rounding {radix : ℕ} (hr : 0 < radix) (levels value : ℕ)
    (estimate : ℕ → ℕ)
    (hestimate : ∀ i ≤ levels,
      estimate i = value / radix ^ i ∨ estimate i = value / radix ^ i + 1) :
    reconstruct radix levels estimate = value ∨ reconstruct radix levels estimate = value + 1 := by
  induction levels generalizing value estimate with
  | zero => simpa [reconstruct] using hestimate 0 (by omega)
  | succ levels ih =>
      exact extend_correctBlock_of_rounding hr
        (ih (value / radix) _ fun i hi => by
          simpa only [Nat.div_div_eq_div_mul, ← pow_succ'] using hestimate (i + 1) (by omega))
        (by simpa using hestimate 0 (by omega))

end Cslib.Circuits.Boolean.ApproximateCount
