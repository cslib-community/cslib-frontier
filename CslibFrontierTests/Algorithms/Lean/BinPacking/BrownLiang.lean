/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Algorithms.Lean.BinPacking.BrownLiang

/-!
# The Brown–Liang lower bound: examples

These kernel-checked examples (using no `native_decide`) exercise
`CslibFrontier.Algorithms.Lean.BinPacking.BrownLiang`:

1. The instance. Each size times its denominator is `D = 3263442`, one more than the capacity; a
   bin holds `1806`, `42`, `6`, `2` and `1` items of the five sizes but not one more, and one
   item of each size fits exactly.
2. The certificate on the tight bins of the linear program: each has weight equal to its bound.
3. The arithmetic of the bound: the total weight `1303 * 1806` against
   `∑ⱼ yⱼ * brownLiangOpt j = 1527918` is the ratio `56029 / 36379`, which lies strictly between
   Brown and Liang's `1.53635` and van Vliet's `1.5401474`.
4. The theorems instantiated: the optima for `m = 1`, the phase bound for First Fit, and the
   ratio violation for `p / q = 154 / 100 = 1.54`.
-/

namespace CslibFrontierTests.BinPacking.BrownLiang

open Cslib.Algorithms.Lean.BinPacking

/-! ### 1. The instance -/

/-- Each size is `3263442 / d` for its Sylvester denominator `d`. -/
example : brownLiangSizes.zipWith (· * ·) [1807, 43, 7, 3, 2] = List.replicate 5 3263442 := by
  decide

/-- At most `1806`, `42`, `6`, `2` and `1` items of the five sizes fit into a bin. -/
example : 1806 * 1806 ≤ 3263441 ∧ 3263441 < 1807 * 1806 ∧ 42 * 75894 ≤ 3263441 ∧
    3263441 < 43 * 75894 ∧ 6 * 466206 ≤ 3263441 ∧ 3263441 < 7 * 466206 ∧
    2 * 1087814 ≤ 3263441 ∧ 3263441 < 3 * 1087814 ∧ 1631721 ≤ 3263441 ∧
    3263441 < 2 * 1631721 := by
  decide

/-- One item of each size fills a bin exactly. -/
example : brownLiangSizes.sum = 3263441 := by decide

/-! ### 2. The certificate on tight bins -/

/-- `714` items of the smallest size and `26` of the second fit and weigh `1806`, the bound for a
bin opened in the first phase. -/
example : 714 * 1806 + 26 * 75894 ≤ 3263441 ∧ 714 * 1 + 26 * 42 = 42 + 252 + 504 + 504 + 504 := by
  decide

/-- A bin with six items of each of the second and third sizes weighs `1764`, the bound for a bin
opened in the second phase. -/
example : ((List.replicate 6 75894 ++ List.replicate 6 466206).map brownLiangWeight).sum =
    252 + 504 + 504 + 504 := by
  decide

/-- Two items of each of the third and fourth sizes weigh `1512`, the bound for a bin opened in
the third phase; one item of each of the two largest sizes weighs `1008`. -/
example : ([466206, 466206, 1087814, 1087814].map brownLiangWeight).sum = 504 + 504 + 504 ∧
    ([1087814, 1631721].map brownLiangWeight).sum = 504 + 504 := by
  decide

/-- The certificate applied to the bin with one item of each size. -/
example : (brownLiangSizes.map brownLiangWeight).sum ≤
    ∑ j : Fin 5, brownLiangMult j *
      (brownLiangSizes.any (· ∈ brownLiangSizes.take (j + 1))).toNat :=
  sum_map_brownLiangWeight_le (by decide)

/-! ### 3. The arithmetic of the bound -/

example : brownLiangMult 0 * brownLiangOpt 0 + brownLiangMult 1 * brownLiangOpt 1 +
    brownLiangMult 2 * brownLiangOpt 2 + brownLiangMult 3 * brownLiangOpt 3 +
    brownLiangMult 4 * brownLiangOpt 4 = 1527918 := by
  decide

example : 1303 * 1806 * 36379 = 56029 * 1527918 := by decide

/-- `1.53635 < 56029 / 36379 < 1.5401474`. -/
example : 153635 * 36379 < 56029 * 100000 ∧ 56029 * 10000000 < 15401474 * 36379 := by decide

/-! ### 4. The theorems instantiated -/

/-- For `m = 1`, the input stopped after the third phase fits into `301` bins and no fewer. -/
example : ∃ Q, IsPacking 3263441 (brownLiangInput (1806 * 1) 2) Q ∧ Q.length = 301 :=
  exists_isPacking_brownLiangInput 1 2

example {Q : List (List ℕ)} (hQ : IsPacking 3263441 (brownLiangInput (1806 * 1) 2) Q) :
    301 ≤ Q.length :=
  le_length_of_isPacking_brownLiangInput hQ

/-- First Fit uses at least `56029 / 36379` times the optimum after some phase of the input with
`1806` items per phase. -/
example : ∃ j : Fin 5, 56029 * (brownLiangOpt j * 1) ≤
    36379 * ((firstFitPacker 3263441).run (brownLiangInput (1806 * 1) j)).length :=
  (firstFitPacker 3263441).brown_liang_lower_bound 1

/-- No online packer has asymptotic ratio `1.54`. -/
example (A : OnlinePacker 3263441) (c : ℕ) :
    ∃ (l : List ℕ) (Q : List (List ℕ)), IsPacking 3263441 l Q ∧
      (∀ Q', IsPacking 3263441 l Q' → Q.length ≤ Q'.length) ∧
      154 * Q.length + c < 100 * (A.run l).length :=
  A.brown_liang_exists_ratio_violation_of_lt (by decide) c

end CslibFrontierTests.BinPacking.BrownLiang
