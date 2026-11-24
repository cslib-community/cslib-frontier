/-
Copyright (c) 2026 Mayank Rathee, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee, Samuel Schlesinger
-/

import CslibFrontier.Crypto.Protocols.PolynomialCommitment.LigeroProximity
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

/-!
# Non-vacuous finite-field witness tests for interleaved Reed–Solomon proximity and Ligero IOPs

Exercises `Cslib.Code.interleavedLinear`, `minDist_interleavedLinear`,
`exists_mem_interleavedLinear_hammingDist_le_iff`, the universal `d / 3` linear-code proximity
bound (`toOuterMeasure_sum_smul_close_le_of_three_mul_lt_minDist`), the Reed–Solomon unique-decoding
`d / 2` proximity and extraction bounds (`toOuterMeasure_sum_smul_reedSolomon_close_le`,
`exists_unique_mem_interleavedLinear_reedSolomon`), and the Ligero cheating-prover proximity and
evaluation soundness theorems (`ligeroProximityReduction_reedSolomon_complete`,
`ligeroProximityReduction_reedSolomon_sound`, `toOuterMeasure_ligeroEvalCheck_false_le`) over
`ZMod 7`, `ZMod 11`, and `ZMod 17`:

1. **Minimum distance preservation** (`ZMod 7`, `n = 7, k = 3, d = 5`):
   `minDist (interleavedLinear (Fin 3) (reedSolomon id 3)) = 5`.
2. **Row-wise close vs. interleaved far boundary in the `d / 3` regime** (`ZMod 11`, `n = 7, k = 3,
   d = 5, e = 1`, `3 * 1 < 5`): a `2 × 7` word whose two rows each have weight `1 ≤ e` on
   *disjoint* columns (`0` and `1`) is strictly `1`-far from the interleaved code and satisfies the
   non-vacuous bound `≤ 2 / 11 < 1`.
3. **Strict `d / 3 < e < d / 2` Reed–Solomon unique-decoding regime** (`ZMod 11`, `n = 6, k = 2,
   d = 5, e = 2`, where `2 * e + k = 6 ≤ 6` holds while `3 * e = 6 > 5` fails `d / 3`):
   * Negative witness: disjoint `2`-column row corruptions (`hammingDist = 4 > 2`) have uniform row
     combination `2`-close to `reedSolomon` with probability `≤ 6 / 11 < 1`.
   * Positive witness: shared `2`-column corruptions on `{0, 1}` achieve probability `1 > 6 / 11`
     and uniquely recover the true interleaved Reed–Solomon codeword via
     `exists_unique_mem_interleavedLinear_reedSolomon`.
4. **End-to-end Ligero proximity reduction and cheating-prover `ligeroEvalCheck` soundness**
   (`ZMod 17`, `n = 6, k = 2, e = 2, q = 3`): non-vacuous `< 1` soundness error `65 / 136 < 1`
   against arbitrary provers on a concrete far matrix, and `≤ 1 / 8 < 1` acceptance probability
   against *every* cheating vector `v : Fin 2 → ZMod 17` on a false linear evaluation of an
   `e`-corrupted matrix.
-/

namespace CslibFrontierTests.InterleavedReedSolomon

open Cslib Cslib.Code Cslib.Crypto.Protocols Cslib.Interactive Cslib.Probability Polynomial
open scoped BigOperators ENNReal Matrix NNReal

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-! ### 1. Minimum distance of an interleaved Reed–Solomon code over `ZMod 7` -/

theorem test_minDist_interleavedLinear_zmod7 :
    minDist (interleavedLinear (Fin 3) (reedSolomon (id : ZMod 7 → ZMod 7) 3) :
      Set (ZMod 7 → Fin 3 → ZMod 7)) = 5 := by
  rw [minDist_interleavedLinear, minDist_reedSolomon Function.injective_id (by omega)
    (by simp [ZMod.card])]
  simp [ZMod.card]

/-! ### 2. Universal `d / 3` bound (`n = 7, k = 3, d = 5, e = 1`) over `ZMod 11` -/

def pts7_11 : Fin 7 → ZMod 11 := fun i => (i.val : ZMod 11)

lemma pts7_11_injective : Function.Injective pts7_11 := by
  decide

/-- Each row has weight `1 ≤ 1` (so each row alone is `1`-close to `0 ∈ reedSolomon pts7_11 3`),
but the errors occur in disjoint columns `0` and `1`. -/
def farW_d3 : Fin 7 → Fin 2 → ZMod 11 :=
  fun i r => if i.val = 0 ∧ r.val = 0 then 1 else if i.val = 1 ∧ r.val = 1 then 1 else 0

lemma farW_d3_not_close :
    ∀ V ∈ interleavedLinear (Fin 2) (reedSolomon pts7_11 3), 1 < hammingDist farW_d3 V := by
  intro V hV
  by_contra hle
  have hle1 : hammingDist farW_d3 V ≤ 1 := Nat.le_of_not_lt hle
  have hrow_dist (r : Fin 2) : hammingDist (fun i => farW_d3 i r) (fun i => V i r) ≤ 1 := by
    refine le_trans (Finset.card_le_card fun i hi => ?_) hle1
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact fun hEq => hi (congrFun hEq r)
  have hrow0 : (fun i => V i 0) = 0 :=
    eq_of_hammingDist_le_reedSolomon (f := fun i => farW_d3 i 0) pts7_11_injective
      (e := 1) (by simp) (hV 0) (Submodule.zero_mem _) (hrow_dist 0) (by decide)
  have hrow1 : (fun i => V i 1) = 0 :=
    eq_of_hammingDist_le_reedSolomon (f := fun i => farW_d3 i 1) pts7_11_injective
      (e := 1) (by simp) (hV 1) (Submodule.zero_mem _) (hrow_dist 1) (by decide)
  have hV0 : V = 0 := by
    funext i r
    fin_cases r
    · exact congrFun hrow0 i
    · exact congrFun hrow1 i
  rw [hV0] at hle1
  have hdist2 : hammingDist farW_d3 0 = 2 := by decide
  omega

theorem test_d3_interleaved_bound_nonvacuous :
    (PMF.uniformOfFintype (Fin 2 → ZMod 11)).toOuterMeasure
        {z | ∃ c ∈ reedSolomon pts7_11 3,
          hammingDist (fun i => ∑ r : Fin 2, z r • farW_d3 i r) c ≤ 1} ≤ 2 / 11 ∧
      ((2 : ℝ≥0∞) / 11 < 1) := by
  have hmin : 3 * (1 : ℕ∞) < minDist (reedSolomon pts7_11 3 : Set (Fin 7 → ZMod 11)) := by
    rw [minDist_reedSolomon pts7_11_injective (by omega) (by simp)]
    norm_num
  have hlt1 : (2 : ℝ≥0∞) / 11 < 1 := by
    have hnn : ((2 : ℝ≥0) / 11) < 1 := by norm_num
    simpa [ENNReal.coe_div (by norm_num : (11 : ℝ≥0) ≠ 0)] using ENNReal.coe_lt_coe.2 hnn
  refine ⟨?_, hlt1⟩
  simpa [ZMod.card] using toOuterMeasure_sum_smul_close_le_of_three_mul_lt_minDist hmin
    farW_d3_not_close

/-! ### 3. Strict `d / 3 < e < d / 2` Reed–Solomon regime (`n = 6, k = 2, d = 5, e = 2`) -/

def pts6_11 : Fin 6 → ZMod 11 := fun i => (i.val : ZMod 11)

lemma pts6_11_injective : Function.Injective pts6_11 := by
  decide

/-- Row `0` corrupts columns `{0, 1}` and row `1` corrupts columns `{2, 3}`: each row is at
distance `2` from `0 ∈ reedSolomon pts6_11 2`, while column-Hamming distance is `4 > 2`. -/
def farW_d2 : Fin 6 → Fin 2 → ZMod 11 :=
  fun i r => if i.val < 2 ∧ r.val = 0 then 1 else if (i.val = 2 ∨ i.val = 3) ∧ r.val = 1 then 1
    else 0

lemma farW_d2_not_close :
    ∀ V ∈ interleavedLinear (Fin 2) (reedSolomon pts6_11 2), 2 < hammingDist farW_d2 V := by
  intro V hV
  by_contra hle
  have hle2 : hammingDist farW_d2 V ≤ 2 := Nat.le_of_not_lt hle
  have hrow_dist (r : Fin 2) : hammingDist (fun i => farW_d2 i r) (fun i => V i r) ≤ 2 := by
    refine le_trans (Finset.card_le_card fun i hi => ?_) hle2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact fun hEq => hi (congrFun hEq r)
  have hrow0 : (fun i => V i 0) = 0 :=
    eq_of_hammingDist_le_reedSolomon (f := fun i => farW_d2 i 0) pts6_11_injective
      (e := 2) (by simp) (hV 0) (Submodule.zero_mem _) (hrow_dist 0) (by decide)
  have hrow1 : (fun i => V i 1) = 0 :=
    eq_of_hammingDist_le_reedSolomon (f := fun i => farW_d2 i 1) pts6_11_injective
      (e := 2) (by simp) (hV 1) (Submodule.zero_mem _) (hrow_dist 1) (by decide)
  have hV0 : V = 0 := by
    funext i r
    fin_cases r
    · exact congrFun hrow0 i
    · exact congrFun hrow1 i
  rw [hV0] at hle2
  have hdist4 : hammingDist farW_d2 0 = 4 := by decide
  omega

theorem test_rs_unique_d2_negative_witness :
    (PMF.uniformOfFintype (Fin 2 → ZMod 11)).toOuterMeasure
        {z | ∃ c ∈ reedSolomon pts6_11 2,
          hammingDist (fun i => ∑ r : Fin 2, z r • farW_d2 i r) c ≤ 2} ≤ 6 / 11 ∧
      ((6 : ℝ≥0∞) / 11 < 1) := by
  have hlt1 : (6 : ℝ≥0∞) / 11 < 1 := by
    have hnn : ((6 : ℝ≥0) / 11) < 1 := by norm_num
    simpa [ENNReal.coe_div (by norm_num : (11 : ℝ≥0) ≠ 0)] using ENNReal.coe_lt_coe.2 hnn
  refine ⟨?_, hlt1⟩
  simpa [ZMod.card] using toOuterMeasure_sum_smul_reedSolomon_close_le pts6_11_injective
    (e := 2) (k := 2) (by simp) farW_d2_not_close

/-- True interleaved codeword with rows evaluating `2 X + 1` and `3 X + 4` over `pts6_11`. -/
def trueV_d2 : Fin 6 → Fin 2 → ZMod 11 :=
  fun i r => if r.val = 0 then 2 * pts6_11 i + 1 else 3 * pts6_11 i + 4

lemma trueV_d2_mem : trueV_d2 ∈ interleavedLinear (Fin 2) (reedSolomon pts6_11 2) := by
  intro r
  fin_cases r
  · change (fun i => trueV_d2 i 0) ∈ reedSolomon pts6_11 2
    have hrow : (fun i => trueV_d2 i 0) =
        fun i => (C (2 : ZMod 11) * X + C 1).eval (pts6_11 i) := by
      funext i
      simp [trueV_d2]
    rw [hrow]
    refine eval_mem_reedSolomon pts6_11 (p := C (2 : ZMod 11) * X + C 1) ?_
    exact (degree_add_le _ _).trans_lt (max_lt
      ((degree_C_mul_X_le 2).trans_lt (by norm_num))
      (degree_C_le.trans_lt (by norm_num)))
  · change (fun i => trueV_d2 i 1) ∈ reedSolomon pts6_11 2
    have hrow : (fun i => trueV_d2 i 1) =
        fun i => (C (3 : ZMod 11) * X + C 4).eval (pts6_11 i) := by
      funext i
      simp [trueV_d2]
    rw [hrow]
    refine eval_mem_reedSolomon pts6_11 (p := C (3 : ZMod 11) * X + C 4) ?_
    exact (degree_add_le _ _).trans_lt (max_lt
      ((degree_C_mul_X_le 3).trans_lt (by norm_num))
      (degree_C_le.trans_lt (by norm_num)))

/-- Corrupted matrix differing from `trueV_d2` on the shared `2`-column set `{0, 1}`. -/
def closeW_d2 : Fin 6 → Fin 2 → ZMod 11 :=
  fun i r => if i.val < 2 then 0 else trueV_d2 i r

theorem test_rs_unique_d2_positive_recovery :
    (∃! V : Fin 6 → Fin 2 → ZMod 11,
      V ∈ interleavedLinear (Fin 2) (reedSolomon pts6_11 2) ∧ hammingDist closeW_d2 V ≤ 2) ∧
    (∀ V, V ∈ interleavedLinear (Fin 2) (reedSolomon pts6_11 2) → hammingDist closeW_d2 V ≤ 2 →
      V = trueV_d2) := by
  have hdist : hammingDist closeW_d2 trueV_d2 ≤ 2 := by decide
  have hall : {z : Fin 2 → ZMod 11 | ∃ c ∈ reedSolomon pts6_11 2,
      hammingDist (fun i => ∑ r : Fin 2, z r • closeW_d2 i r) c ≤ 2} = Set.univ := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact ⟨fun i => ∑ r : Fin 2, z r • trueV_d2 i r,
      sum_smul_mem_of_mem_interleavedLinear trueV_d2_mem z,
      (hammingDist_sum_smul_le z closeW_d2 trueV_d2).trans hdist⟩
  have hprob : (Fintype.card (Fin 6) : ℝ≥0∞) / (Fintype.card (ZMod 11) : ℝ≥0∞) <
      (PMF.uniformOfFintype (Fin 2 → ZMod 11)).toOuterMeasure
        {z | ∃ c ∈ reedSolomon pts6_11 2,
          hammingDist (fun i => ∑ r : Fin 2, z r • closeW_d2 i r) c ≤ 2} := by
    rw [hall]
    simp only [PMF.toOuterMeasure_apply, Set.indicator_univ, PMF.tsum_coe, Fintype.card_fin,
      ZMod.card]
    have hnn : ((6 : ℝ≥0) / 11) < 1 := by norm_num
    simpa [ENNReal.coe_div (by norm_num : (11 : ℝ≥0) ≠ 0)] using ENNReal.coe_lt_coe.2 hnn
  have hexu := exists_unique_mem_interleavedLinear_reedSolomon pts6_11_injective
    (e := 2) (k := 2) (by simp) hprob
  refine ⟨hexu, fun V hV hd => ?_⟩
  obtain ⟨V₀, -, huniq⟩ := hexu
  exact (huniq V ⟨hV, hd⟩).trans (huniq trueV_d2 ⟨trueV_d2_mem, hdist⟩).symm

/-! ### 4. Ligero Reed–Solomon proximity IOP & cheating-prover `ligeroEvalCheck` over `ZMod 17` -/

def pts6_17 : Fin 6 → ZMod 17 := fun i => (i.val : ZMod 17)

lemma pts6_17_injective : Function.Injective pts6_17 := by
  decide

def farM_17 : Matrix (Fin 2) (Fin 6) (ZMod 17) :=
  Matrix.of fun r i => if i.val < 2 ∧ r.val = 0 then 1
    else if (i.val = 2 ∨ i.val = 3) ∧ r.val = 1 then 1 else 0

lemma farM_17_not_mem_proximityLang :
    farM_17 ∉ ligeroProximityLang 2 (reedSolomonGenerator pts6_17 2) 2 := by
  rintro ⟨V, hV, hle2⟩
  rw [codeOfGenerator_reedSolomonGenerator] at hV
  have hrow_dist (r : Fin 2) :
      hammingDist (fun i => Function.swap farM_17 i r) (fun i => V i r) ≤ 2 := by
    refine le_trans (Finset.card_le_card fun i hi => ?_) hle2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact fun hEq => hi (congrFun hEq r)
  have hrow0 : (fun i => V i 0) = 0 :=
    eq_of_hammingDist_le_reedSolomon (f := fun i => Function.swap farM_17 i 0) pts6_17_injective
      (e := 2) (by simp) (hV 0) (Submodule.zero_mem _) (hrow_dist 0) (by decide)
  have hrow1 : (fun i => V i 1) = 0 :=
    eq_of_hammingDist_le_reedSolomon (f := fun i => Function.swap farM_17 i 1) pts6_17_injective
      (e := 2) (by simp) (hV 1) (Submodule.zero_mem _) (hrow_dist 1) (by decide)
  have hV0 : V = 0 := by
    funext i r
    fin_cases r
    · exact congrFun hrow0 i
    · exact congrFun hrow1 i
  rw [hV0] at hle2
  have hdist4 : hammingDist (Function.swap farM_17) 0 = 4 := by decide
  omega

/-- Over `ZMod 17` (`n = 6, k = 2, e = 2, q = 3`), the Reed–Solomon Ligero proximity reduction is
perfectly complete and rejects `farM_17` against **every** prover strategy except with probability
at most `6 / 17 + (3 / 6) ^ 3 = 65 / 136 < 1`. -/
theorem test_ligeroProximityReduction_reedSolomon_zmod17 :
    (ligeroProximityReduction 2 (reedSolomonGenerator pts6_17 2) 3).Complete
        World.plain (ligeroCodewordRel 2 (reedSolomonGenerator pts6_17 2)) Accept 0 ∧
      farM_17 ∉ ligeroProximityLang 2 (reedSolomonGenerator pts6_17 2) 2 ∧
      (∀ (α : Type) (P : ProbOracleComp OracleSpec.empty
          (ProverStrategy (ProbOracleComp OracleSpec.empty)
            (ligeroProximitySpec 2 2 6 3 (ZMod 17)) α)),
        (World.plain.eval
            ((ligeroProximityReduction 2
              (reedSolomonGenerator pts6_17 2) 3).verifier.execute farM_17 P)).toOuterMeasure
          {r | ∃ x' ∈ (Set.univ : Set Unit), r.output = some x'} ≤ 65 / 136) ∧
      ((65 : ℝ≥0∞) / 136 < 1) := by
  have hlt1 : (65 : ℝ≥0∞) / 136 < 1 := by
    have hnn : ((65 : ℝ≥0) / 136) < 1 := by norm_num
    simpa [ENNReal.coe_div (by norm_num : (136 : ℝ≥0) ≠ 0)] using ENNReal.coe_lt_coe.2 hnn
  have hval : ((6 : ℝ≥0∞) / 17) + ((3 : ℝ≥0∞) / 6) ^ 3 = 65 / 136 := by
    have hnn : ((6 : ℝ≥0) / 17) + ((3 : ℝ≥0) / 6) ^ 3 = 65 / 136 := by norm_num
    simpa [ENNReal.coe_add, ENNReal.coe_pow,
      ENNReal.coe_div (by norm_num : (17 : ℝ≥0) ≠ 0),
      ENNReal.coe_div (by norm_num : (6 : ℝ≥0) ≠ 0),
      ENNReal.coe_div (by norm_num : (136 : ℝ≥0) ≠ 0)] using congrArg (↑· : ℝ≥0 → ℝ≥0∞) hnn
  refine ⟨ligeroProximityReduction_complete 2 _ 3, farM_17_not_mem_proximityLang,
    fun α P => ?_, hlt1⟩
  have hsnd := ligeroProximityReduction_reedSolomon_sound 2 (q := 3) (e := 2) (k := 2)
    pts6_17_injective (by omega) farM_17 farM_17_not_mem_proximityLang α P
  refine hsnd.trans_eq ?_
  simpa only [ZMod.card, show (6 - (2 + 1) : ℕ) = 3 by omega, Nat.cast_ofNat] using hval

/-- Witness matrix `U` over `ZMod 17` and a corrupted matrix `corruptM_17` at column distance `2`
from `U * reedSolomonGenerator pts6_17 2`: for the false claim `ligeroEval U ![1, 1] ![1, 0] = 0`
(true value is `1 + 3 = 4`), **every** cheating response `v : Fin 2 → ZMod 17` passes `3` uniform
column checks with probability at most `(3 / 6) ^ 3 = 1 / 8 < 1`. -/
def witnessU_17 : Matrix (Fin 2) (Fin 2) (ZMod 17) := !![1, 2; 3, 4]

def corruptM_17 : Matrix (Fin 2) (Fin 6) (ZMod 17) :=
  Matrix.of fun r j =>
    if j.val < 2 then 0 else (witnessU_17 * reedSolomonGenerator pts6_17 2) r j

theorem test_cheating_prover_ligeroEvalCheck_zmod17 (v : Fin 2 → ZMod 17) :
    (PMF.uniformOfFintype (Fin 3 → Fin 6)).toOuterMeasure
        {Q | ∀ t : Fin 3, ligeroEvalCheck (reedSolomonGenerator pts6_17 2) corruptM_17
          ![1, 1] ![1, 0] 0 v (Q t) = true} ≤ 1 / 8 ∧
      ((1 : ℝ≥0∞) / 8 < 1) := by
  have hmin : 2 * (2 : ℕ∞) <
      minDist (codeOfGenerator (reedSolomonGenerator pts6_17 2) : Set (Fin 6 → ZMod 17)) := by
    rw [codeOfGenerator_reedSolomonGenerator,
      minDist_reedSolomon pts6_17_injective (by omega) (by simp)]
    norm_num
  have hinj := vecMul_reedSolomonGenerator_injective pts6_17_injective (k := 2) (by omega)
  have hclose : hammingDist (Function.swap corruptM_17)
      (Function.swap (witnessU_17 * reedSolomonGenerator pts6_17 2)) ≤ 2 := by
    decide
  have hfalse : ligeroEval witnessU_17 ![1, 1] ![1, 0] ≠ 0 := by
    decide
  have hlt1 : (1 : ℝ≥0∞) / 8 < 1 := by simp
  have hpow : ((3 : ℝ≥0∞) / 6) ^ 3 = 1 / 8 := by
    have hnn : ((3 : ℝ≥0) / 6) ^ 3 = 1 / 8 := by norm_num
    simpa [ENNReal.coe_pow,
      ENNReal.coe_div (by norm_num : (6 : ℝ≥0) ≠ 0),
      ENNReal.coe_div (by norm_num : (8 : ℝ≥0) ≠ 0)] using congrArg (↑· : ℝ≥0 → ℝ≥0∞) hnn
  refine ⟨?_, hlt1⟩
  refine (toOuterMeasure_ligeroEvalCheck_false_le (q := 3)
    (reedSolomonGenerator pts6_17 2) hmin hinj hclose ![1, 1] ![1, 0] 0 hfalse v).trans_eq ?_
  simpa only [show (6 - (2 + 1) : ℕ) = 3 by omega, Nat.cast_ofNat] using hpow

end CslibFrontierTests.InterleavedReedSolomon
