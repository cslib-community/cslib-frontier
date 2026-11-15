/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.CellProbe.OuterGame
public import CslibFrontier.DataStructure.Dictionary.CellProbe.LowerBound
public import CslibFrontierTests.DictLowerBoundDist
import Mathlib.Tactic.NormNum

/-!
# Multi-Level Cell-Probe Lower Bounds and Outer Communication Game Tests

Kernel-checked concrete instances, parameter specializations, and consistency checks for
`CslibFrontier.DataStructure.Dictionary.CellProbe.OuterGame` and
`CslibFrontier.DataStructure.Dictionary.CellProbe.LowerBound`:

1. Concrete dictionary scheme instantiation: `directDictScheme.toIndexed` from
   `DictLowerBoundDist.lean` unconditionally satisfies `validHistoriesUpTo 4 2 2 M` for all `M`,
   instantiating `det_expectedSeqProbes_ge_linear` on both `insertQueryDeleteDist` (query-inclusive)
   and `insertDeleteDist` (update-only).
2. Concrete `OuterGame` combinatorial and distribution checks:
   (a) multi-level partition identity `prod_choose_partition_mul_pow_factorial`;
   (b) mode-distribution identifications `modeDist_true` and `modeDist_false`.
3. Parameter specialization and signature consistency for Theorem 1.1 / 3.1: preserving the
   full universal lower-bound clause on `det_expectedSeqProbes_ge_of_iterLog_redundancy` and its
   `Ω(n log* n)` specialization `det_expectedSeqProbes_ge_iterLogStar`, alongside randomized
   zero-error variants.
4. Parameter specialization and signature consistency for Theorem 1.2 / 6.1:
   `det_expectedSeqProbes_ge_of_sublinear_redundancy` and combined
   `det_expectedSeqProbes_ge_iterLogStar_add_log_div`.
5. Parameter specialization and signature consistency for Theorem 1.3: update-only
   `insertDeleteDist` bounds: Theorem 1.3(1) `det_expectedSeqProbes_update_ge_iterLog` /
   `expectedSeqProbes_update_ge_iterLog` and their `Ω(n log* n)` specializations
   `det_expectedSeqProbes_update_ge_iterLogStar` / `expectedSeqProbes_update_ge_iterLogStar`,
   alongside Theorem 1.3(2) `det_expectedSeqProbes_update_ge_sublinear`,
   `expectedSeqProbes_update_ge_sublinear`, and combined trade-offs.
6. Space benchmark bridge `optBits_le_benchmarkBits_add` evaluation on concrete parameters.
-/

public section

namespace CslibFrontierTests.DictLowerBoundMultilevel

open Cslib Cslib.CellProbe Cslib.DataStructure
open Cslib.DataStructure.Dictionary Cslib.DataStructure.Dictionary.CellProbe
open CslibFrontierTests.DictLowerBoundDist

/-! ### 1. Concrete Scheme Instantiation of Linear Lower Bounds -/

/-- Concrete exact instantiation of `det_expectedSeqProbes_ge_linear` in query-inclusive mode
on `directDictScheme.toIndexed` at `U = 4, V = 2, n = 2`, discharging every hypothesis. -/
theorem det_linear_bound_query_inclusive_directDict :
    (1 : ℝ) ≤
      ∑' ops, (insertQueryDeleteDist 4 2 2 (by omega) (by omega) ops).toReal *
        (directDictScheme.toIndexed.seqProbes ops : ℝ) := by
  have hl := det_expectedSeqProbes_ge_linear true (U := 4) (V := 2) (n := 2)
    (by omega) (by omega) (D_det := directDictScheme.toIndexed)
    (directDictScheme_all_histories 9)
  have h_mode : modeDist true 4 2 2 (by omega) (by omega) =
      insertQueryDeleteDist 4 2 2 (by omega) (by omega) := modeDist_true 4 2 2 (by omega) (by omega)
  rw [h_mode] at hl
  norm_num at hl ⊢
  exact hl

/-- Concrete exact instantiation of `det_expectedSeqProbes_ge_linear` in update-only mode
on `directDictScheme.toIndexed` at `U = 4, V = 2, n = 2`, discharging every hypothesis. -/
theorem det_linear_bound_update_only_directDict :
    (1 : ℝ) ≤
      ∑' ops, (insertDeleteDist 4 2 2 (by omega) (by omega) ops).toReal *
        (directDictScheme.toIndexed.seqProbes ops : ℝ) := by
  have hl := det_expectedSeqProbes_ge_linear false (U := 4) (V := 2) (n := 2)
    (by omega) (by omega) (D_det := directDictScheme.toIndexed)
    (directDictScheme_all_histories 7)
  have h_mode : modeDist false 4 2 2 (by omega) (by omega) =
      insertDeleteDist 4 2 2 (by omega) (by omega) := modeDist_false 4 2 2 (by omega) (by omega)
  rw [h_mode] at hl
  norm_num at hl ⊢
  exact hl

/-! ### 2. Outer Game Combinatorial and Distribution Verifications -/

/-- Concrete verification of the Outer Game partition formula
`prod_choose_partition_mul_pow_factorial` at `F = 2, m = 2`:
`((4.choose 2) * (2.choose 2) = 6 * 1 = 6 = 24 / 4 = 4! / (2! ^ 2))`. -/
theorem outerGame_partition_formula_concrete :
    (∏ i : Fin 2, ((2 - i.val) * 2).choose 2) * Nat.factorial 2 ^ 2 = (2 * 2).factorial :=
  prod_choose_partition_mul_pow_factorial 2 2

/-- Exact distribution equivalence between mode distributions and the concrete
`insertQueryDeleteDist` and `insertDeleteDist` samplers. -/
theorem outerGame_modeDist_concrete :
    modeDist true 4 2 2 (by omega) (by omega) =
      insertQueryDeleteDist 4 2 2 (by omega) (by omega) ∧
    modeDist false 4 2 2 (by omega) (by omega) =
      insertDeleteDist 4 2 2 (by omega) (by omega) :=
  ⟨modeDist_true 4 2 2 (by omega) (by omega), modeDist_false 4 2 2 (by omega) (by omega)⟩

/-! ### 3. Parameter Specialization and Signature Consistency for Theorem 1.1 / 3.1 -/

/-- Parameter specialization and signature consistency for deterministic Theorem 1.1 / 3.1:
preserves the universal lower-bound clause of `det_expectedSeqProbes_ge_of_iterLog_redundancy`
at `α = 1, c_R = 1, c_w = 1`. -/
theorem det_theorem1_1_specialization :
    ∃ c : ℝ, 0 < c ∧
      ∀ {U V n k cells w : ℕ} (hn : 2 ≤ n) (hU : 4 * n ≤ U)
        (_hU_poly : (n : ℝ) ^ ((1 : ℝ) + 1) ≤ (U : ℝ)) (hV : 1 ≤ V)
        (_hk_lo : 1 ≤ k) (_hk_hi : k ≤ Nat.logStar n)
        (_hw : (w : ℝ) ≤ 1 * (Real.logb 2 U + Real.logb 2 V))
        (_hspace : ((cells * w : ℕ) : ℝ) ≤
          benchmarkBits U V n + 1 * (n : ℝ) * ((max (Nat.iterLog k n) 1 : ℕ) : ℝ))
        {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
        (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
          (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2),
        c * (n : ℝ) * (k : ℝ) ≤
          ∑' ops, (insertQueryDeleteDist U V n
            (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops).toReal *
            (D_det.seqProbes ops : ℝ) :=
  det_expectedSeqProbes_ge_of_iterLog_redundancy (α := 1) (c_R := 1) (c_w := 1)
    (by norm_num) (by norm_num) (by norm_num)

/-- Parameter specialization and signature consistency for zero-error randomized Theorem 1.1:
retains the full universal bound at `α = 1, c_R = 1, c_w = 1`. -/
theorem rand_theorem1_1_specialization :
    ∃ c : ℝ, 0 < c ∧
        ∀ {U V n k cells w : ℕ} (hn : 2 ≤ n) (hU : 4 * n ≤ U)
          (_hU_poly : (n : ℝ) ^ ((1 : ℝ) + 1) ≤ (U : ℝ)) (hV : 1 ≤ V)
          (_hk_lo : 1 ≤ k) (_hk_hi : k ≤ Nat.logStar n)
          (_hw : (w : ℝ) ≤ 1 * (Real.logb 2 U + Real.logb 2 V))
          (_hspace : ((cells * w : ℕ) : ℝ) ≤
            benchmarkBits U V n + 1 * (n : ℝ) * ((max (Nat.iterLog k n) 1 : ℕ) : ℝ))
          (P : Cslib.CellProbe.Randomized.Scheme (Dynamic.Op U) Dynamic.Op.Result cells w)
          (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
            ((Dynamic.spec U V n).toObliviousSequenceSpec (Dictionary.empty U)).Contract
              ops ((P.runSeq ops).map Prod.fst)),
          ENNReal.ofReal (c * (n : ℝ) * (k : ℝ)) ≤
            ∑' ops, insertQueryDeleteDist U V n
              (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops *
              P.expectedSeqProbes ops :=
  expectedSeqProbes_ge_of_iterLog_redundancy (α := 1) (c_R := 1) (c_w := 1)
    (by norm_num) (by norm_num) (by norm_num)

/-- Parameter specialization and signature consistency for deterministic `Ω(n log* n)` lower
bound retaining the full universal clause at `α = 1, c_R = 1, c_w = 1`. -/
theorem det_theorem1_1_logStar_specialization :
    ∃ c : ℝ, 0 < c ∧
        ∀ {U V n cells w : ℕ} (hn : 2 ≤ n) (hU : 4 * n ≤ U)
          (_hU_poly : (n : ℝ) ^ ((1 : ℝ) + 1) ≤ (U : ℝ)) (hV : 1 ≤ V)
          (_hw : (w : ℝ) ≤ 1 * (Real.logb 2 U + Real.logb 2 V))
          (_hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + 1 * (n : ℝ))
          {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
          (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
            (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2),
          c * (n : ℝ) * (Nat.logStar n : ℝ) ≤
            ∑' ops, (insertQueryDeleteDist U V n
              (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops).toReal *
              (D_det.seqProbes ops : ℝ) :=
  det_expectedSeqProbes_ge_iterLogStar (α := 1) (c_R := 1) (c_w := 1)
    (by norm_num) (by norm_num) (by norm_num)

/-- Parameter specialization and signature consistency for randomized `Ω(n log* n)` lower
bound retaining the full universal clause at `α = 1, c_R = 1, c_w = 1`. -/
theorem rand_theorem1_1_logStar_specialization :
    ∃ c : ℝ, 0 < c ∧
        ∀ {U V n cells w : ℕ} (hn : 2 ≤ n) (hU : 4 * n ≤ U)
          (_hU_poly : (n : ℝ) ^ ((1 : ℝ) + 1) ≤ (U : ℝ)) (hV : 1 ≤ V)
          (_hw : (w : ℝ) ≤ 1 * (Real.logb 2 U + Real.logb 2 V))
          (_hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + 1 * (n : ℝ))
          (P : Cslib.CellProbe.Randomized.Scheme (Dynamic.Op U) Dynamic.Op.Result cells w)
          (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
            ((Dynamic.spec U V n).toObliviousSequenceSpec (Dictionary.empty U)).Contract
              ops ((P.runSeq ops).map Prod.fst)),
          ENNReal.ofReal (c * (n : ℝ) * (Nat.logStar n : ℝ)) ≤
            ∑' ops, insertQueryDeleteDist U V n
              (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops *
              P.expectedSeqProbes ops :=
  expectedSeqProbes_ge_iterLogStar (α := 1) (c_R := 1) (c_w := 1)
    (by norm_num) (by norm_num) (by norm_num)

/-! ### 4. Parameter Specialization and Signature Consistency for Theorem 1.2 / 6.1 -/

/-- Parameter specialization and signature consistency for deterministic Theorem 1.2 `Ω(log(n/R))`
bound with universal clause at `α = 1, c_w = 1`. -/
theorem det_theorem1_2_sublinear_specialization :
    ∃ c : ℝ, 0 < c ∧
        ∀ {U V n cells w : ℕ} {R : ℝ} (hn : 2 ≤ n) (hU : 4 * n ≤ U)
          (_hU_poly : (n : ℝ) ^ ((1 : ℝ) + 1) ≤ (U : ℝ)) (hV : 1 ≤ V)
          (_hR_hi : R ≤ (n : ℝ))
          (_hw : (w : ℝ) ≤ 1 * (Real.logb 2 U + Real.logb 2 V))
          (_hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R)
          {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
          (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
            (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2),
          c * (n : ℝ) * Real.logb 2 ((n : ℝ) / max R 1) ≤
            ∑' ops, (insertQueryDeleteDist U V n
              (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops).toReal *
              (D_det.seqProbes ops : ℝ) :=
  det_expectedSeqProbes_ge_of_sublinear_redundancy (α := 1) (c_w := 1) (by norm_num) (by norm_num)

/-- Parameter specialization and signature consistency for randomized Theorem 1.2 `Ω(log(n/R))`
bound with universal clause at `α = 1, c_w = 1`. -/
theorem rand_theorem1_2_sublinear_specialization :
    ∃ c : ℝ, 0 < c ∧
        ∀ {U V n cells w : ℕ} {R : ℝ} (hn : 2 ≤ n) (hU : 4 * n ≤ U)
          (_hU_poly : (n : ℝ) ^ ((1 : ℝ) + 1) ≤ (U : ℝ)) (hV : 1 ≤ V)
          (_hR_hi : R ≤ (n : ℝ))
          (_hw : (w : ℝ) ≤ 1 * (Real.logb 2 U + Real.logb 2 V))
          (_hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R)
          (P : Cslib.CellProbe.Randomized.Scheme (Dynamic.Op U) Dynamic.Op.Result cells w)
          (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
            ((Dynamic.spec U V n).toObliviousSequenceSpec (Dictionary.empty U)).Contract
              ops ((P.runSeq ops).map Prod.fst)),
          ENNReal.ofReal (c * (n : ℝ) * Real.logb 2 ((n : ℝ) / max R 1)) ≤
            ∑' ops, insertQueryDeleteDist U V n
              (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops *
              P.expectedSeqProbes ops :=
  expectedSeqProbes_ge_of_sublinear_redundancy (α := 1) (c_w := 1) (by norm_num) (by norm_num)

/-- Parameter specialization and signature consistency for deterministic combined
`Ω(log* n + log(n/R))` bound with universal clause at `α = 1, c_R = 1, c_w = 1`. -/
theorem det_theorem1_2_combined_specialization :
    ∃ c : ℝ, 0 < c ∧
        ∀ {U V n cells w : ℕ} {R : ℝ} (hn : 2 ≤ n) (hU : 4 * n ≤ U)
          (_hU_poly : (n : ℝ) ^ ((1 : ℝ) + 1) ≤ (U : ℝ)) (hV : 1 ≤ V)
          (_hR_hi : R ≤ 1 * (n : ℝ))
          (_hw : (w : ℝ) ≤ 1 * (Real.logb 2 U + Real.logb 2 V))
          (_hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R)
          {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
          (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
            (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2),
          c * (n : ℝ) * ((Nat.logStar n : ℝ) + max 0 (Real.logb 2 ((n : ℝ) / max R 1))) ≤
            ∑' ops, (insertQueryDeleteDist U V n
              (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops).toReal *
              (D_det.seqProbes ops : ℝ) :=
  det_expectedSeqProbes_ge_iterLogStar_add_log_div (α := 1) (c_R := 1) (c_w := 1)
    (by norm_num) (by norm_num) (by norm_num)

/-- Parameter specialization and signature consistency for randomized combined
`Ω(log* n + log(n/R))` bound with universal clause at `α = 1, c_R = 1, c_w = 1`. -/
theorem rand_theorem1_2_combined_specialization :
    ∃ c : ℝ, 0 < c ∧
        ∀ {U V n cells w : ℕ} {R : ℝ} (hn : 2 ≤ n) (hU : 4 * n ≤ U)
          (_hU_poly : (n : ℝ) ^ ((1 : ℝ) + 1) ≤ (U : ℝ)) (hV : 1 ≤ V)
          (_hR_hi : R ≤ 1 * (n : ℝ))
          (_hw : (w : ℝ) ≤ 1 * (Real.logb 2 U + Real.logb 2 V))
          (_hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R)
          (P : Cslib.CellProbe.Randomized.Scheme (Dynamic.Op U) Dynamic.Op.Result cells w)
          (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
            ((Dynamic.spec U V n).toObliviousSequenceSpec (Dictionary.empty U)).Contract
              ops ((P.runSeq ops).map Prod.fst)),
          ENNReal.ofReal (c * (n : ℝ) *
            ((Nat.logStar n : ℝ) + max 0 (Real.logb 2 ((n : ℝ) / max R 1)))) ≤
            ∑' ops, insertQueryDeleteDist U V n
              (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops *
              P.expectedSeqProbes ops :=
  expectedSeqProbes_ge_iterLogStar_add_log_div (α := 1) (c_R := 1) (c_w := 1)
    (by norm_num) (by norm_num) (by norm_num)

/-! ### 5. Parameter Specialization and Signature Consistency for Theorem 1.3 (Update-Only) -/

/-- Parameter specialization and signature consistency for deterministic Theorem 1.3(1)
`Ω(n * k)` update-only bound at `α_V = 1, c_R = 1, c_w = 1`. -/
theorem det_theorem1_3_iterLog_specialization :
    ∃ c : ℝ, 0 < c ∧
      ∀ {U V n k cells w : ℕ} (hn : 2 ≤ n) (hU : 3 * n ≤ U) (hV : 1 ≤ V)
        (_hV_lo : (U : ℝ) ^ ((2 : ℝ) + 1) ≤ (V : ℝ) * (n : ℝ) ^ 2)
        (_hk_lo : 1 ≤ k) (_hk_hi : k ≤ Nat.logStar n)
        (_hw : (w : ℝ) ≤ 1 * (Real.logb 2 U + Real.logb 2 V))
        (_hspace : ((cells * w : ℕ) : ℝ) ≤
          benchmarkBits U V n + 1 * (n : ℝ) * ((max (Nat.iterLog k n) 1 : ℕ) : ℝ))
        {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
        (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (3 * n + 1),
          (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2),
        c * (n : ℝ) * (k : ℝ) ≤
          ∑' ops, (insertDeleteDist U V n
            (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops).toReal *
            (D_det.seqProbes ops : ℝ) :=
  det_expectedSeqProbes_update_ge_iterLog (α_V := 1) (c_R := 1) (c_w := 1)
    (by norm_num) (by norm_num) (by norm_num)

/-- Parameter specialization and signature consistency for zero-error randomized Theorem 1.3(1)
`Ω(n * k)` update-only bound at `α_V = 1, c_R = 1, c_w = 1`. -/
theorem rand_theorem1_3_iterLog_specialization :
    ∃ c : ℝ, 0 < c ∧
      ∀ {U V n k cells w : ℕ} (hn : 2 ≤ n) (hU : 3 * n ≤ U) (hV : 1 ≤ V)
        (_hV_lo : (U : ℝ) ^ ((2 : ℝ) + 1) ≤ (V : ℝ) * (n : ℝ) ^ 2)
        (_hk_lo : 1 ≤ k) (_hk_hi : k ≤ Nat.logStar n)
        (_hw : (w : ℝ) ≤ 1 * (Real.logb 2 U + Real.logb 2 V))
        (_hspace : ((cells * w : ℕ) : ℝ) ≤
          benchmarkBits U V n + 1 * (n : ℝ) * ((max (Nat.iterLog k n) 1 : ℕ) : ℝ))
        (P : Cslib.CellProbe.Randomized.Scheme (Dynamic.Op U) Dynamic.Op.Result cells w)
        (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (3 * n + 1),
          ((Dynamic.spec U V n).toObliviousSequenceSpec (Dictionary.empty U)).Contract
            ops ((P.runSeq ops).map Prod.fst)),
        ENNReal.ofReal (c * (n : ℝ) * (k : ℝ)) ≤
          ∑' ops, insertDeleteDist U V n
            (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops *
            P.expectedSeqProbes ops :=
  expectedSeqProbes_update_ge_iterLog (α_V := 1) (c_R := 1) (c_w := 1)
    (by norm_num) (by norm_num) (by norm_num)

/-- Parameter specialization and signature consistency for deterministic Theorem 1.3(1)
`Ω(n * log* n)` update-only bound at `α_V = 1, c_R = 1, c_w = 1`. -/
theorem det_theorem1_3_logStar_specialization :
    ∃ c : ℝ, 0 < c ∧
      ∀ {U V n cells w : ℕ} (hn : 2 ≤ n) (hU : 3 * n ≤ U) (hV : 1 ≤ V)
        (_hV_lo : (U : ℝ) ^ ((2 : ℝ) + 1) ≤ (V : ℝ) * (n : ℝ) ^ 2)
        (_hw : (w : ℝ) ≤ 1 * (Real.logb 2 U + Real.logb 2 V))
        (_hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + 1 * (n : ℝ))
        {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
        (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (3 * n + 1),
          (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2),
        c * (n : ℝ) * (Nat.logStar n : ℝ) ≤
          ∑' ops, (insertDeleteDist U V n
            (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops).toReal *
            (D_det.seqProbes ops : ℝ) :=
  det_expectedSeqProbes_update_ge_iterLogStar (α_V := 1) (c_R := 1) (c_w := 1)
    (by norm_num) (by norm_num) (by norm_num)

/-- Parameter specialization and signature consistency for randomized Theorem 1.3(1)
`Ω(n * log* n)` update-only bound at `α_V = 1, c_R = 1, c_w = 1`. -/
theorem rand_theorem1_3_logStar_specialization :
    ∃ c : ℝ, 0 < c ∧
      ∀ {U V n cells w : ℕ} (hn : 2 ≤ n) (hU : 3 * n ≤ U) (hV : 1 ≤ V)
        (_hV_lo : (U : ℝ) ^ ((2 : ℝ) + 1) ≤ (V : ℝ) * (n : ℝ) ^ 2)
        (_hw : (w : ℝ) ≤ 1 * (Real.logb 2 U + Real.logb 2 V))
        (_hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + 1 * (n : ℝ))
        (P : Cslib.CellProbe.Randomized.Scheme (Dynamic.Op U) Dynamic.Op.Result cells w)
        (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (3 * n + 1),
          ((Dynamic.spec U V n).toObliviousSequenceSpec (Dictionary.empty U)).Contract
            ops ((P.runSeq ops).map Prod.fst)),
        ENNReal.ofReal (c * (n : ℝ) * (Nat.logStar n : ℝ)) ≤
          ∑' ops, insertDeleteDist U V n
            (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops *
            P.expectedSeqProbes ops :=
  expectedSeqProbes_update_ge_iterLogStar (α_V := 1) (c_R := 1) (c_w := 1)
    (by norm_num) (by norm_num) (by norm_num)

/-- Parameter specialization and signature consistency for deterministic Theorem 1.3(2)
`Ω(log(n/R))` update-only bound at `α_V = 1, c_w = 1`. -/
theorem det_theorem1_3_sublinear_specialization :
    ∃ c : ℝ, 0 < c ∧
        ∀ {U V n cells w : ℕ} {R : ℝ} (hn : 2 ≤ n) (hU : 3 * n ≤ U) (hV : 1 ≤ V)
          (_hV_lo : (U : ℝ) ^ ((2 : ℝ) + 1) ≤ (V : ℝ) * (n : ℝ) ^ 2)
          (_hR_hi : R ≤ (n : ℝ))
          (_hw : (w : ℝ) ≤ 1 * (Real.logb 2 U + Real.logb 2 V))
          (_hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R)
          {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
          (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (3 * n + 1),
            (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2),
          c * (n : ℝ) * Real.logb 2 ((n : ℝ) / max R 1) ≤
            ∑' ops, (insertDeleteDist U V n
              (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops).toReal *
              (D_det.seqProbes ops : ℝ) :=
  det_expectedSeqProbes_update_ge_sublinear (α_V := 1) (c_w := 1) (by norm_num) (by norm_num)

/-- Parameter specialization and signature consistency for randomized Theorem 1.3(2)
`Ω(log(n/R))` update-only bound at `α_V = 1, c_w = 1`. -/
theorem rand_theorem1_3_sublinear_specialization :
    ∃ c : ℝ, 0 < c ∧
        ∀ {U V n cells w : ℕ} {R : ℝ} (hn : 2 ≤ n) (hU : 3 * n ≤ U) (hV : 1 ≤ V)
          (_hV_lo : (U : ℝ) ^ ((2 : ℝ) + 1) ≤ (V : ℝ) * (n : ℝ) ^ 2)
          (_hR_hi : R ≤ (n : ℝ))
          (_hw : (w : ℝ) ≤ 1 * (Real.logb 2 U + Real.logb 2 V))
          (_hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R)
          (P : Cslib.CellProbe.Randomized.Scheme (Dynamic.Op U) Dynamic.Op.Result cells w)
          (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (3 * n + 1),
            ((Dynamic.spec U V n).toObliviousSequenceSpec (Dictionary.empty U)).Contract
              ops ((P.runSeq ops).map Prod.fst)),
          ENNReal.ofReal (c * (n : ℝ) * Real.logb 2 ((n : ℝ) / max R 1)) ≤
            ∑' ops, insertDeleteDist U V n
              (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops *
              P.expectedSeqProbes ops :=
  expectedSeqProbes_update_ge_sublinear (α_V := 1) (c_w := 1) (by norm_num) (by norm_num)

/-- Parameter specialization and signature consistency for deterministic update-only
`Ω(log* n + log(n/R))` bound at `α_V = 1, c_R = 1, c_w = 1`. -/
theorem det_theorem1_3_combined_specialization :
    ∃ c : ℝ, 0 < c ∧
        ∀ {U V n cells w : ℕ} {R : ℝ} (hn : 2 ≤ n) (hU : 3 * n ≤ U) (hV : 1 ≤ V)
          (_hV_lo : (U : ℝ) ^ ((2 : ℝ) + 1) ≤ (V : ℝ) * (n : ℝ) ^ 2)
          (_hR_hi : R ≤ 1 * (n : ℝ))
          (_hw : (w : ℝ) ≤ 1 * (Real.logb 2 U + Real.logb 2 V))
          (_hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R)
          {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
          (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (3 * n + 1),
            (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2),
          c * (n : ℝ) * ((Nat.logStar n : ℝ) + max 0 (Real.logb 2 ((n : ℝ) / max R 1))) ≤
            ∑' ops, (insertDeleteDist U V n
              (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops).toReal *
              (D_det.seqProbes ops : ℝ) :=
  det_expectedSeqProbes_update_ge_iterLogStar_add_log_div (α_V := 1) (c_R := 1) (c_w := 1)
    (by norm_num) (by norm_num) (by norm_num)

/-- Parameter specialization and signature consistency for randomized update-only
`Ω(log* n + log(n/R))` bound at `α_V = 1, c_R = 1, c_w = 1`. -/
theorem rand_theorem1_3_combined_specialization :
    ∃ c : ℝ, 0 < c ∧
        ∀ {U V n cells w : ℕ} {R : ℝ} (hn : 2 ≤ n) (hU : 3 * n ≤ U) (hV : 1 ≤ V)
          (_hV_lo : (U : ℝ) ^ ((2 : ℝ) + 1) ≤ (V : ℝ) * (n : ℝ) ^ 2)
          (_hR_hi : R ≤ 1 * (n : ℝ))
          (_hw : (w : ℝ) ≤ 1 * (Real.logb 2 U + Real.logb 2 V))
          (_hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R)
          (P : Cslib.CellProbe.Randomized.Scheme (Dynamic.Op U) Dynamic.Op.Result cells w)
          (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (3 * n + 1),
            ((Dynamic.spec U V n).toObliviousSequenceSpec (Dictionary.empty U)).Contract
              ops ((P.runSeq ops).map Prod.fst)),
          ENNReal.ofReal (c * (n : ℝ) *
            ((Nat.logStar n : ℝ) + max 0 (Real.logb 2 ((n : ℝ) / max R 1)))) ≤
            ∑' ops, insertDeleteDist U V n
              (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops *
              P.expectedSeqProbes ops :=
  expectedSeqProbes_update_ge_iterLogStar_add_log_div (α_V := 1) (c_R := 1) (c_w := 1)
    (by norm_num) (by norm_num) (by norm_num)

/-! ### 6. Space Benchmark Bridge Evaluation -/

/-- Concrete check of `optBits_le_benchmarkBits_add` at `U = 8, V = 2, n = 4`. -/
theorem optBits_bridge_check_concrete :
    (Dynamic.optBits 8 2 4 : ℝ) ≤ benchmarkBits 8 2 4 + 4 + 1 :=
  optBits_le_benchmarkBits_add (by omega) (by omega)

end CslibFrontierTests.DictLowerBoundMultilevel
