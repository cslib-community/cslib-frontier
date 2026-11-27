/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Protocols.Cipher.LinearCryptanalysis
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Tests for linear cryptanalysis by majority vote

Checks `linearKeyBitEstimate` on Boneh–Shoup's `t = 3` examples and on ties (`t = 2`, `t = 0`),
verifies `HasLinearRelation` and Lemma 4.3 on a keyed permutation (`ε = 1 / 2`) and a biased
cipher (`ε = 1 / 4`, with exact `t = 2` probability `3 / 4`), derives the printed bound
`1 - Real.exp (-(t * ε ^ 2 / 2))` and the `> 86 / 100` remark for `t > 4 / ε ^ 2`, and checks
that the bound fails for a negative bias.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.LinearCryptanalysis

open Cslib Cslib.Crypto.LinearCryptanalysis Cslib.Probability.PMF

/-! ### Concrete Majority and Plurality Tie Checks -/

-- Boneh–Shoup `t = 3` examples: `[0, 0, 1] ↦ 0` and `[0, 1, 1] ↦ 1`.
example :
    linearKeyBitEstimate ({0} : Finset (Fin 1)) ∅
      (fun i : Fin 3 => (fun _ => decide (i.val = 2), fun _ => false)) = false := by
  decide

example :
    linearKeyBitEstimate ({0} : Finset (Fin 1)) ∅
      (fun i : Fin 3 => (fun _ => decide (i.val ≠ 0), fun _ => false)) = true := by
  decide

-- `ProbComp.plurality false` tie-breaking: earliest maximal vote wins; `t = 0` yields `false`.
example :
    linearKeyBitEstimate ({0} : Finset (Fin 1)) ∅
      (fun i : Fin 2 => (fun _ => decide (i.val = 0), fun _ => false)) = true := by
  decide

example :
    linearKeyBitEstimate ({0} : Finset (Fin 1)) ∅
      (fun i : Fin 2 => (fun _ => decide (i.val = 1), fun _ => false)) = false := by
  decide

example :
    linearKeyBitEstimate ({0} : Finset (Fin 1)) ∅
      (fun i : Fin 0 => Fin.elim0 i) = false := by
  decide

/-! ### Keyed Permutation (`ε = 1 / 2`) and Biased Cipher (`ε = 1 / 4`) -/

/-- Exact linear cipher given by XORing a 1-bit key via `Equiv.addRight`. -/
def addRightCipher (k m : BitString 1) : BitString 1 := Equiv.addRight k m

theorem hasLinearRelation_addRightCipher :
    HasLinearRelation addRightCipher {0} {0} {0} (1 / 2) := by
  intro k
  rw [toOuterMeasure_uniformOfFintype_toReal]
  simp only [Set.mem_ofPred_eq]
  have hcard :
      (Finset.univ.filter fun m : BitString 1 =>
        (parityOn {0} m ^^ parityOn {0} (addRightCipher k m)) = parityOn {0} k).card = 2 := by
    revert k
    decide
  rw [hcard]
  simp only [Fintype.card_pi, Fintype.card_bool, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, pow_one, Nat.cast_ofNat]
  norm_num

/-- Biased 2-bit cipher with 1-bit key: `m 0 ^^ E k m 0 = k 0` on `3 / 4` of plaintexts. -/
def biasedCipher (k : BitString 1) (m : BitString 2) : BitString 2 :=
  fun i => if i.val = 0 then if !m 0 && !m 1 then !(m 0 ^^ k 0) else m 0 ^^ k 0 else m 1

theorem hasLinearRelation_biasedCipher :
    HasLinearRelation biasedCipher {0} {0} {0} (1 / 4) := by
  intro k
  rw [toOuterMeasure_uniformOfFintype_toReal]
  simp only [Set.mem_ofPred_eq]
  have hcard :
      (Finset.univ.filter fun m : BitString 2 =>
        (parityOn {0} m ^^ parityOn {0} (biasedCipher k m)) = parityOn {0} k).card = 3 := by
    revert k
    decide
  rw [hcard]
  simp only [Fintype.card_pi, Fintype.card_bool, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  norm_num

example (k : BitString 1) (t : ℕ) :
    1 - Real.exp (-2 * t * (1 / 4 : ℝ) ^ 2) ≤
      ((uniformOfFintype (Fin t → BitString 2)).toOuterMeasure
        {m : Fin t → BitString 2 |
          linearKeyBitEstimate {0} {0} (fun i => (m i, biasedCipher k (m i))) =
            parityOn {0} k}).toReal :=
  hasLinearRelation_biasedCipher.prob_linearKeyBitEstimate_ge (by norm_num) k t

-- Under `ProbComp.plurality false`, `(G, B)` ties resolve to `G` and `(B, G)` ties resolve to `B`,
-- so `biasedCipher` at `t = 2` has exact recovery probability `(9 + 3) / 16 = 3 / 4`.
example (k : BitString 1) :
    ((uniformOfFintype (Fin 2 → BitString 2)).toOuterMeasure
      {m : Fin 2 → BitString 2 |
        linearKeyBitEstimate {0} {0} (fun i => (m i, biasedCipher k (m i))) =
          parityOn {0} k}).toReal = 3 / 4 := by
  rw [toOuterMeasure_uniformOfFintype_toReal]
  simp only [Set.mem_ofPred_eq]
  have hcard :
      (Finset.univ.filter fun m : Fin 2 → BitString 2 =>
        linearKeyBitEstimate {0} {0} (fun i => (m i, biasedCipher k (m i))) =
          parityOn {0} k).card = 12 := by
    revert k
    decide
  rw [hcard]
  simp only [Fintype.card_pi, Fintype.card_bool, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  norm_num

/-! ### Printed Eq. (4.15), 86% Remark, and Negative-Bias Counterexample -/

/-- The printed Boneh–Shoup bound (4.15), implied by `prob_linearKeyBitEstimate_ge`. -/
example {h n : ℕ}
    {E : BitString h → BitString n → BitString n} {S₀ S₁ : Finset (Fin n)}
    {S₂ : Finset (Fin h)} {ε : ℝ} (hrel : HasLinearRelation E S₀ S₁ S₂ ε) (hε : 0 ≤ ε)
    (k : BitString h) (t : ℕ) :
    1 - Real.exp (-((t : ℝ) * ε ^ 2 / 2)) ≤
      ((uniformOfFintype (Fin t → BitString n)).toOuterMeasure
        {m : Fin t → BitString n |
          linearKeyBitEstimate S₀ S₁ (fun i => (m i, E k (m i))) = parityOn S₂ k}).toReal := by
  refine le_trans ?_ (hrel.prob_linearKeyBitEstimate_ge hε k t)
  have hte : 0 ≤ (t : ℝ) * ε ^ 2 := by positivity
  have hexp : Real.exp (-2 * t * ε ^ 2) ≤ Real.exp (-((t : ℝ) * ε ^ 2 / 2)) :=
    Real.exp_le_exp.mpr (by linarith)
  linarith

/-- Boneh–Shoup remark after Lemma 4.3: more than `4 / ε ^ 2` pairs give probability
`> 86 / 100`. -/
example {h n : ℕ}
    {E : BitString h → BitString n → BitString n} {S₀ S₁ : Finset (Fin n)}
    {S₂ : Finset (Fin h)} {ε : ℝ} (hrel : HasLinearRelation E S₀ S₁ S₂ ε) (hε : 0 < ε)
    (k : BitString h) {t : ℕ} (ht : 4 / ε ^ 2 < t) :
    (86 / 100 : ℝ) <
      ((uniformOfFintype (Fin t → BitString n)).toOuterMeasure
        {m : Fin t → BitString n |
          linearKeyBitEstimate S₀ S₁ (fun i => (m i, E k (m i))) = parityOn S₂ k}).toReal := by
  have hbound := hrel.prob_linearKeyBitEstimate_ge hε.le k t
  have h4 : 4 < (t : ℝ) * ε ^ 2 := (div_lt_iff₀ (sq_pos_of_pos hε)).mp ht
  have hexp_lt : Real.exp (-2 * t * ε ^ 2) < Real.exp (-2) := by
    rw [Real.exp_lt_exp]
    linarith
  have hm2 : Real.exp (-2) < 14 / 100 := by
    have he1 : (27 / 10 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
    have hexp2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    rw [Real.exp_neg, inv_lt_iff_one_lt_mul₀ (Real.exp_pos 2), hexp2]
    nlinarith
  linarith

-- Omitting `0 ≤ ε` falsifies both the `2 * t * ε ^ 2` bound and the printed (4.15) bound.
example :
    let E : BitString 1 → BitString 1 → BitString 1 := fun k m _ => !(m 0 ^^ k 0)
    HasLinearRelation E {0} {0} {0} (-1 / 2) ∧
      ((uniformOfFintype (Fin 1 → BitString 1)).toOuterMeasure
        {m : Fin 1 → BitString 1 |
          linearKeyBitEstimate {0} {0} (fun i => (m i, E (fun _ => false) (m i))) =
            parityOn {0} (fun _ : Fin 1 => false)}).toReal = 0 ∧
      (0 : ℝ) < 1 - Real.exp (-2 * (1 : ℕ) * (-1 / 2 : ℝ) ^ 2) ∧
      (0 : ℝ) < 1 - Real.exp (-(((1 : ℕ) : ℝ) * (-1 / 2 : ℝ) ^ 2 / 2)) := by
  refine ⟨fun k => ?_, ?_, ?_, ?_⟩
  · have hzero : (1 / 2 : ℝ) + (-1 / 2) = 0 := by norm_num
    rw [hzero]
    exact ENNReal.toReal_nonneg
  · rw [toOuterMeasure_uniformOfFintype_toReal]
    simp only [Set.mem_ofPred_eq]
    have hcard :
        (Finset.univ.filter fun m : Fin 1 → BitString 1 =>
          linearKeyBitEstimate {0} {0}
            (fun i => (m i, (fun _ : Fin 1 => !(m i 0 ^^ false)))) =
              parityOn {0} (fun _ : Fin 1 => false)).card = 0 := by
      decide
    rw [hcard]
    simp
  · have : Real.exp (-2 * ((1 : ℕ) : ℝ) * (-1 / 2 : ℝ) ^ 2) < 1 :=
      Real.exp_lt_one_iff.mpr (by norm_num)
    linarith
  · have : Real.exp (-(((1 : ℕ) : ℝ) * (-1 / 2 : ℝ) ^ 2 / 2)) < 1 :=
      Real.exp_lt_one_iff.mpr (by norm_num)
    linarith

/-! ### Axiom Guard -/

/--
info: 'Cslib.Crypto.LinearCryptanalysis.HasLinearRelation.prob_linearKeyBitEstimate_ge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms HasLinearRelation.prob_linearKeyBitEstimate_ge

end CslibFrontierTests.Crypto.LinearCryptanalysis
