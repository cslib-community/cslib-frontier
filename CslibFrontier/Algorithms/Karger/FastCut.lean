/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Karger.Graph
public import CslibFrontier.Languages.Probabilistic.QueryCount.Support
import CslibFrontier.Foundations.Analysis.ENNRealNatDiv
import CslibFrontier.Foundations.Analysis.ENNRealOneSubInvPow

/-!
# Mathematical recurrences and quadratic potential for Karger–Stein (`FastCut`)

Combinatorial, arithmetic, and probabilistic foundations for the Karger–Stein recursive global
minimum cut algorithm (`[KargerStein1996]`, Section 4, Figure 6, Lemmas 4.1–4.3, and the
minimum-cut-value part of Theorem 4.4; paraphrase). The definitions are plain arithmetic: the
recursion of the specification (`CslibFrontier.Algorithms.Lean.Karger.FastCut`) and the word-RAM
program (`CslibFrontier.Algorithms.WordRAM.KargerStein`) both use them, and the time, query and
scratch budgets are the ones the program is charged against.

## Design notes and deviations from `[KargerStein1996]`

1. **Integer contraction threshold (`fastCutThreshold`):** `[KargerStein1996]`, Section 4, Figure 6
   contracts each branch to `⌈k / √2 + 1⌉` vertices so that `(t * (t - 1)) / (k * (k - 1)) ≥ 1 / 2`
   (Section 4, Lemma 4.3). We instead define `fastCutThreshold k` as the smallest integer `t ≥ 2`
   satisfying `k * (k - 1) ≤ 2 * t * (t - 1)`. This integer deviation directly enforces Lemma 4.3's
   `≥ 1 / 2` per-branch survival inequality without square roots or divisions; it is never larger
   than `⌈k / √2 + 1⌉` and is strictly smaller at e.g. `k = 8` (`t = 6` vs `7`).
2. **Base case at `k ≤ 6`, as in the source:** each leaf runs one random contraction down to
   `2` vertices, the base case `G' ← Contract(G, 2)` of `[KargerStein1996]`, Section 4,
   Figure 6. The cutoff follows equation (2) and the remark at the end of the proof of Lemma 4.3
   (recurse for `n ≥ 7`); Figure 6 itself tests "fewer than 6 vertices". A leaf keeps a fixed
   minimum cut with probability `≥ 2 / (k * (k - 1)) ≥ 2 / 30`, equation (2)'s base-case bound
   `1 / 15`. The `15` in `1 / (Nat.log 2 n + 15)` is the source's constant: the proof of
   Lemma 4.3 sets `z₀ = 59` and shows `z_k < 59 + 2 * k` for `k ≥ 1`, so
   `p_k = 4 / (z_k + 1) ≥ 2 / (30 + k)`; at depth at most `2 * Nat.log 2 n` this is
   `1 / (Nat.log 2 n + 15)`.
3. **Concrete Word-RAM constants and trial schedule (`fastCutTrials`):** `[KargerStein1996]`,
   Section 4, Lemmas 4.1–4.3 state asymptotic `O(n ^ 2 log n)` time, `O(n ^ 2)` space and
   `Ω(1 / log n)` single-tree success probability, and the proof of Theorem 4.4 repeats the
   algorithm `O(log ^ 2 n)` times; the explicit coefficients in `fastCutNodeTime` and
   `fastCutScratch`, the trial schedule `fastCutTrials n = (Nat.log 2 n + 15) * (Nat.log 2 n + 2)`
   and the `1 / (2 * n)` failure target are concrete parameter choices of this formalization.
4. **Elementary quadratic potential `Φ(k) = (k - 4) ^ 2`:** `two_mul_pot_threshold_le` proves
   `2 * (fastCutThreshold k - 4) ^ 2 ≤ (k - 4) ^ 2` for all `k ≥ 7` via integer arithmetic
   (`49 * 2 = 98 < 100 = 10 ^ 2`), replacing real-valued recurrence unrolling in
   `[KargerStein1996]`, Section 4, Lemmas 4.1–4.3.

## Main definitions

* `Cslib.Algorithms.Karger.fastCutThreshold`: smallest integer `t ≥ 2` satisfying
  `k * (k - 1) ≤ 2 * t * (t - 1)`.
* `Cslib.Algorithms.Karger.fastCutDepth`,
  `Cslib.Algorithms.Karger.frameSize`,
  `Cslib.Algorithms.Karger.fastCutScratch`: recursion depth, per-frame memory footprint, and
  root-to-leaf active stack scratch bound.
* `Cslib.Algorithms.Karger.fastCutNodeTime`,
  `Cslib.Algorithms.Karger.fastCutNodeQueries`,
  `Cslib.Algorithms.Karger.fastCutTrials`: explicit time, `rand`-call, and high-probability
  amplification budgets.

## Main results

* `Cslib.Algorithms.Karger.two_mul_pot_threshold_le`: quadratic potential halving
  `2 * (fastCutThreshold k - 4) ^ 2 ≤ (k - 4) ^ 2` for every `k ≥ 7`, proved via integer arithmetic
  without real square roots.
* `Cslib.Algorithms.Karger.fastCutDepth_le_two_mul_log`: recursion depth bound
  `fastCutDepth k ≤ 2 * Nat.log 2 k`.
* `Cslib.Algorithms.Karger.fastCutScratch_le`: total root-to-leaf stack workspace bound
  `fastCutScratch n ≤ 26 * (n * n)` for `n ≥ 2` (`[KargerStein1996]`, Section 4, Lemma 4.2;
  paraphrase).
* `Cslib.Algorithms.Karger.root_hit_prob_eq`: normalize the root-depth success bound to
  `1 / (Nat.log 2 n + 15)` (`[KargerStein1996]`, Section 4, Lemma 4.3; paraphrase).
* `Cslib.Algorithms.Karger.fastCutHighProb_failure_le`: amplified failure bound
  `≤ 1 / (2 * n)` (the minimum-cut-value part of `[KargerStein1996]`, Section 4, Theorem 4.4;
  paraphrase), without `Real.log` or `Real.exp`.

## References

* [D. R. Karger and C. Stein, *A New Approach to the Minimum Cut Problem*][KargerStein1996]
* [M. Mitzenmacher and E. Upfal, *Probability and Computing*][MitzenmacherUpfal2017]
-/

@[expose] public section

namespace Cslib.Algorithms.Karger

open scoped ENNReal
open Cslib.Probability.PMF

/-! ### Pure-integer threshold `fastCutThreshold` and quadratic potential `Φ(k) = (k - 4) ^ 2` -/

/-- Bounded upward search for the smallest `t` satisfying `k * (k - 1) ≤ 2 * t * (t - 1)`. -/
def fastCutThresholdAux (k : ℕ) : ℕ → ℕ → ℕ
  | 0, t => t
  | fuel + 1, t =>
    if 2 * t * (t - 1) < k * (k - 1) then
      fastCutThresholdAux k fuel (t + 1)
    else
      t

/-- Pure-integer Karger–Stein contraction threshold: for `k ≥ 7`, the smallest `t ≥ 2` such that
`k * (k - 1) ≤ 2 * t * (t - 1)`, ensuring `((t * (t - 1)) / (k * (k - 1)) : ℝ≥0∞) ≥ 1 / 2`
(`[KargerStein1996]`, Section 4, Lemma 4.3; paraphrase). This integer deviation from Figure 6's
`⌈k / √2 + 1⌉` is never larger and is strictly smaller at e.g. `k = 8` (`t = 6` vs `7`). -/
def fastCutThreshold (k : ℕ) : ℕ :=
  fastCutThresholdAux k k 2

private theorem mul_pred_le_two_mul_pred_sub_two {k : ℕ} (hk : 4 ≤ k) :
    k * (k - 1) ≤ 2 * (k - 1) * (k - 2) :=
  (Nat.mul_le_mul_right (k - 1) (by omega : k ≤ 2 * (k - 2))).trans_eq (by ring)

private theorem fastCutThresholdAux_spec {k fuel t : ℕ} (hk : 4 ≤ k) (ht : t ≤ k - 1)
    (hfuel : k - 1 ≤ t + fuel) :
    let r := fastCutThresholdAux k fuel t
    t ≤ r ∧ r ≤ k - 1 ∧
    k * (k - 1) ≤ 2 * r * (r - 1) ∧
    ∀ m, t ≤ m → m < r → 2 * m * (m - 1) < k * (k - 1) := by
  induction fuel generalizing t with
  | zero =>
    have ht_eq : t = k - 1 := by omega
    subst ht_eq
    refine ⟨le_rfl, le_rfl, ?_, fun _ hge hlt => absurd hlt (not_lt_of_ge hge)⟩
    have hsub2 : k - 1 - 1 = k - 2 := by omega
    simpa only [fastCutThresholdAux, hsub2] using mul_pred_le_two_mul_pred_sub_two hk
  | succ fuel ih =>
    dsimp only [fastCutThresholdAux]
    by_cases hlt : 2 * t * (t - 1) < k * (k - 1)
    · simp only [hlt, ↓reduceIte]
      have ht_lt : t < k - 1 := by
        by_contra hge
        have heq : t = k - 1 := by omega
        subst heq
        have hsub2 : k - 1 - 1 = k - 2 := by omega
        rw [hsub2] at hlt
        exact absurd (mul_pred_le_two_mul_pred_sub_two hk) (not_le_of_gt hlt)
      rcases ih (t := t + 1) (by omega) (by omega) with ⟨h1, h2, h3, h4⟩
      refine ⟨by omega, h2, h3, fun m htm hmr => ?_⟩
      rcases eq_or_lt_of_le htm with rfl | hgt
      · exact hlt
      · exact h4 m (by omega) hmr
    · simp only [hlt, ↓reduceIte]
      exact ⟨le_rfl, ht, Nat.le_of_not_lt hlt, fun _ hge hlt' => absurd hlt' (not_lt_of_ge hge)⟩

/-- Lower bound `2 ≤ fastCutThreshold k` for `k ≥ 4`. -/
theorem fastCutThreshold_ge_two {k : ℕ} (hk : 4 ≤ k) :
    2 ≤ fastCutThreshold k :=
  (fastCutThresholdAux_spec hk (by omega) (by omega)).1

/-- Upper bound `fastCutThreshold k ≤ k - 1` for `k ≥ 4`. -/
theorem fastCutThreshold_le_pred {k : ℕ} (hk : 4 ≤ k) :
    fastCutThreshold k ≤ k - 1 :=
  (fastCutThresholdAux_spec hk (by omega) (by omega)).2.1

/-- Strict decrease `fastCutThreshold k < k` for `k ≥ 4`. -/
theorem fastCutThreshold_lt {k : ℕ} (hk : 4 ≤ k) :
    fastCutThreshold k < k := by
  have := fastCutThreshold_le_pred hk
  omega

/-- Defining threshold inequality
`k * (k - 1) ≤ 2 * fastCutThreshold k * (fastCutThreshold k - 1)`. -/
theorem fastCutThreshold_spec {k : ℕ} (hk : 4 ≤ k) :
    k * (k - 1) ≤ 2 * fastCutThreshold k * (fastCutThreshold k - 1) :=
  (fastCutThresholdAux_spec hk (by omega) (by omega)).2.2.1

/-- Minimality of `fastCutThreshold k`: every `2 ≤ m < fastCutThreshold k` satisfies
`2 * m * (m - 1) < k * (k - 1)`. -/
theorem fastCutThreshold_lt_of_lt {k m : ℕ} (hk : 4 ≤ k) (hm2 : 2 ≤ m)
    (hmlt : m < fastCutThreshold k) :
    2 * m * (m - 1) < k * (k - 1) :=
  (fastCutThresholdAux_spec hk (by omega) (by omega)).2.2.2 m hm2 hmlt

/-- For `k ≥ 7`, the contraction threshold satisfies `6 ≤ fastCutThreshold k`. -/
theorem fastCutThreshold_ge_six {k : ℕ} (hk : 7 ≤ k) :
    6 ≤ fastCutThreshold k := by
  have hspec := fastCutThreshold_spec (by omega : 4 ≤ k)
  have hk42 : 42 ≤ k * (k - 1) := Nat.mul_le_mul hk (by omega : 6 ≤ k - 1)
  by_contra hlt
  have hle5 : fastCutThreshold k ≤ 5 := by omega
  have hprod : 2 * fastCutThreshold k * (fastCutThreshold k - 1) ≤ 40 := by
    interval_cases fastCutThreshold k <;> decide
  omega

/-- Predecessor minimality inequality
`2 * (fastCutThreshold k - 1) * (fastCutThreshold k - 2) < k * (k - 1)` for `k ≥ 7`. -/
theorem fastCutThreshold_min {k : ℕ} (hk : 7 ≤ k) :
    2 * (fastCutThreshold k - 1) * (fastCutThreshold k - 2) < k * (k - 1) := by
  have h6 := fastCutThreshold_ge_six hk
  have hm := fastCutThreshold_lt_of_lt (k := k) (m := fastCutThreshold k - 1)
    (by omega) (by omega) (by omega)
  have hsub : fastCutThreshold k - 1 - 1 = fastCutThreshold k - 2 := by omega
  rwa [hsub] at hm

/-- **Quadratic potential halving (`Φ(k) = (k - 4) ^ 2`):** for every `k ≥ 7`,
`2 * (fastCutThreshold k - 4) ^ 2 ≤ (k - 4) ^ 2`.
Uses `49 * 2 = 98 < 100 = 10 ^ 2`: if `b ^ 2 < 2 * a ^ 2` (`a = t - 4 ≥ 2`, `b = k - 4 ≥ 3`),
then `(7 * b) ^ 2 < 100 * a ^ 2 = (10 * a) ^ 2`, so `7 * b < 10 * a` and
`b ^ 2 + 7 * b < 2 * a ^ 2 + 10 * a`, contradicting `2 * (t - 1) * (t - 2) < k * (k - 1)`. -/
theorem two_mul_pot_threshold_le {k : ℕ} (hk : 7 ≤ k) :
    2 * (fastCutThreshold k - 4) ^ 2 ≤ (k - 4) ^ 2 := by
  have hmin := fastCutThreshold_min hk
  have h6 := fastCutThreshold_ge_six hk
  obtain ⟨a, ha⟩ : ∃ a, fastCutThreshold k = a + 4 := ⟨fastCutThreshold k - 4, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, k = b + 4 := ⟨k - 4, by omega⟩
  rw [ha, show a + 4 - 1 = a + 3 by omega, show a + 4 - 2 = a + 2 by omega,
    show b + 4 - 1 = b + 3 by omega] at hmin
  rw [ha, Nat.add_sub_cancel, Nat.add_sub_cancel]
  by_contra hgt
  have h7b : 7 * b < 10 * a := (Nat.pow_lt_pow_iff_left (by decide : 2 ≠ 0)).mp (by
    have : 4 ≤ a ^ 2 := Nat.pow_le_pow_left (by omega : 2 ≤ a) 2
    rw [Nat.mul_pow, Nat.mul_pow]; omega)
  rw [show 2 * (a + 3) * (a + 2) = 2 * a ^ 2 + 10 * a + 12 by ring,
    show (b + 4) * (b + 3) = b ^ 2 + 7 * b + 12 by ring] at hmin
  omega

/-- For every `k ≥ 7`, `k ^ 2 ≤ 6 * (k - 4) ^ 2`. -/
theorem sq_le_six_mul_pot {k : ℕ} (hk : 7 ≤ k) :
    k ^ 2 ≤ 6 * (k - 4) ^ 2 := by
  obtain ⟨c, rfl⟩ : ∃ c, k = c + 7 := ⟨k - 7, by omega⟩
  rw [show c + 7 - 4 = c + 3 by omega,
    show (c + 7) ^ 2 = c ^ 2 + 14 * c + 49 by ring,
    show 6 * (c + 3) ^ 2 = 6 * c ^ 2 + 36 * c + 54 by ring]
  omega

/-- For every `k ≥ 7`, `2 * k + 2 ≤ 3 * fastCutThreshold k`, ensuring that linear per-node costs sum
geometrically to `O((k - 4) ^ 2)` across the binary recursion tree. -/
theorem two_mul_add_two_le_three_mul_threshold {k : ℕ} (hk : 7 ≤ k) :
    2 * k + 2 ≤ 3 * fastCutThreshold k := by
  have hspec := fastCutThreshold_spec (by omega : 4 ≤ k)
  have h6 := fastCutThreshold_ge_six hk
  obtain ⟨a, ha⟩ : ∃ a, fastCutThreshold k = a + 6 := ⟨fastCutThreshold k - 6, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, k = b + 7 := ⟨k - 7, by omega⟩
  rw [ha] at hspec ⊢
  rw [show b + 7 - 1 = b + 6 by omega, show a + 6 - 1 = a + 5 by omega,
    show (b + 7) * (b + 6) = b ^ 2 + 13 * b + 42 by ring,
    show 2 * (a + 6) * (a + 5) = 2 * ((a + 6) * (a + 5)) by ring] at hspec
  by_contra hgt
  have hm := Nat.mul_le_mul (show 3 * (a + 6) ≤ 2 * b + 15 by omega)
    (show 3 * (a + 5) ≤ 2 * b + 12 by omega)
  rw [show (3 * (a + 6)) * (3 * (a + 5)) = 9 * ((a + 6) * (a + 5)) by ring,
    show (2 * b + 15) * (2 * b + 12) = 4 * b ^ 2 + 54 * b + 180 by ring] at hm
  omega


/-! ### Recursion depth, stack workspace, query count, and time recurrences -/

/-- Recursion depth of `FastCut` down to the base case `k ≤ 6`. -/
def fastCutDepth (k : ℕ) : ℕ :=
  if h : 7 ≤ k then
    have : fastCutThreshold k < k := fastCutThreshold_lt (by omega)
    fastCutDepth (fastCutThreshold k) + 1
  else
    0
termination_by k

/-- Base-case unfolding of `fastCutDepth` for `k < 7`. -/
theorem fastCutDepth_of_lt_seven {k : ℕ} (hk : k < 7) :
    fastCutDepth k = 0 := by
  rw [fastCutDepth]
  simp only [show ¬7 ≤ k by omega, ↓reduceDIte]

/-- Recursive unfolding of `fastCutDepth` for `k ≥ 7`. -/
theorem fastCutDepth_of_ge_seven {k : ℕ} (hk : 7 ≤ k) :
    fastCutDepth k = fastCutDepth (fastCutThreshold k) + 1 := by
  rw [fastCutDepth]
  simp only [hk, ↓reduceDIte]

/-- For every `k ≥ 7`, `2 * 2 ^ fastCutDepth k ≤ (k - 4) ^ 2`. -/
theorem two_mul_pow_fastCutDepth_le_pot {k : ℕ} (hk : 7 ≤ k) :
    2 * 2 ^ fastCutDepth k ≤ (k - 4) ^ 2 := by
  fun_induction fastCutDepth k with
  | case1 k h _ ih =>
    by_cases ht7 : 7 ≤ fastCutThreshold k
    · calc 2 * 2 ^ (fastCutDepth (fastCutThreshold k) + 1)
          = 2 * (2 * 2 ^ fastCutDepth (fastCutThreshold k)) := by ring
        _ ≤ 2 * (fastCutThreshold k - 4) ^ 2 := Nat.mul_le_mul_left 2 (ih ht7)
        _ ≤ (k - 4) ^ 2 := two_mul_pot_threshold_le h
    · rw [fastCutDepth_of_lt_seven (by omega)]
      exact (Nat.pow_le_pow_left (by omega : 3 ≤ k - 4) 2).trans' (by decide)
  | case2 k h => omega

/-- The recursion depth of `FastCut` on `k` vertices is at most `2 * Nat.log 2 k`. -/
theorem fastCutDepth_le_two_mul_log (k : ℕ) :
    fastCutDepth k ≤ 2 * Nat.log 2 k := by
  by_cases hk : 7 ≤ k
  · set L := Nat.log 2 k
    have hk4_lt : k - 4 < 2 ^ (L + 1) := by
      have : k < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by decide) k; omega
    have hlt_pow : 2 * 2 ^ fastCutDepth k < 2 * 2 ^ (2 * L + 1) :=
      calc 2 * 2 ^ fastCutDepth k ≤ (k - 4) ^ 2 := two_mul_pow_fastCutDepth_le_pot hk
        _ < (2 ^ (L + 1)) ^ 2 := Nat.pow_lt_pow_left hk4_lt (by decide)
        _ = 2 * 2 ^ (2 * L + 1) := by
            rw [← pow_mul, show (L + 1) * 2 = 2 * L + 1 + 1 by omega, pow_succ']
    have hlt_exp : fastCutDepth k < 2 * L + 1 :=
      (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (by omega)
    omega
  · rw [fastCutDepth_of_lt_seven (by omega)]
    exact Nat.zero_le _

/-- Word count of one explicit stack frame at active vertex count `k`:
4 header words (`parentFp`, `k`, `stage`, `savedVal1`), immutable `k × k` frame matrix,
working `k × k` contraction matrix, and `k`-word degree buffer. -/
def frameSize (k : ℕ) : ℕ :=
  4 + 2 * (k * k) + k

/-- Total stack scratch words along any root-to-leaf active path starting at `k` vertices. -/
def fastCutScratch (k : ℕ) : ℕ :=
  if h : 7 ≤ k then
    have : fastCutThreshold k < k := fastCutThreshold_lt (by omega)
    frameSize k + fastCutScratch (fastCutThreshold k)
  else
    frameSize k
termination_by k

/-- Base-case unfolding of `fastCutScratch` for `k < 7`. -/
theorem fastCutScratch_of_lt_seven {k : ℕ} (hk : k < 7) :
    fastCutScratch k = frameSize k := by
  rw [fastCutScratch]
  simp only [show ¬7 ≤ k by omega, ↓reduceDIte]

/-- Recursive unfolding of `fastCutScratch` for `k ≥ 7`. -/
theorem fastCutScratch_of_ge_seven {k : ℕ} (hk : 7 ≤ k) :
    fastCutScratch k = frameSize k + fastCutScratch (fastCutThreshold k) := by
  rw [fastCutScratch]
  simp only [hk, ↓reduceDIte]

private theorem frameSize_le_thirteen_mul_pot {k : ℕ} (hk : 7 ≤ k) :
    frameSize k ≤ 13 * (k - 4) ^ 2 := by
  unfold frameSize
  obtain ⟨c, rfl⟩ : ∃ c, k = c + 7 := ⟨k - 7, by omega⟩
  rw [show c + 7 - 4 = c + 3 by omega,
    show 4 + 2 * ((c + 7) * (c + 7)) + (c + 7) = 2 * c ^ 2 + 29 * c + 109 by ring,
    show 13 * (c + 3) ^ 2 = 13 * c ^ 2 + 78 * c + 117 by ring]
  omega

/-- Potential-based upper bound `fastCutScratch k ≤ 26 * (k - 4) ^ 2` for `k ≥ 7`. -/
theorem fastCutScratch_le_pot {k : ℕ} (hk : 7 ≤ k) :
    fastCutScratch k ≤ 26 * (k - 4) ^ 2 := by
  fun_induction fastCutScratch k with
  | case1 k h _ ih =>
    have hfs := frameSize_le_thirteen_mul_pot h
    have ht6 : 6 ≤ fastCutThreshold k := fastCutThreshold_ge_six h
    by_cases ht7 : 7 ≤ fastCutThreshold k
    · have hih := ih ht7
      have hpot := two_mul_pot_threshold_le h
      omega
    · have ht_eq : fastCutThreshold k = 6 := by omega
      have hbase : fastCutScratch (fastCutThreshold k) = 82 := by
        rw [fastCutScratch_of_lt_seven (by omega), ht_eq]; decide
      have h9 : 9 ≤ (k - 4) ^ 2 := Nat.pow_le_pow_left (by omega : 3 ≤ k - 4) 2
      omega
  | case2 k h => omega

/-- Total stack workspace for `FastCut` on `n ≥ 2` vertices is at most `26 * (n * n)` words. -/
theorem fastCutScratch_le {n : ℕ} (hn : 2 ≤ n) :
    fastCutScratch n ≤ 26 * (n * n) := by
  by_cases hn7 : 7 ≤ n
  · have hpot := fastCutScratch_le_pot hn7
    have hle := (Nat.pow_le_pow_left (Nat.sub_le n 4) 2).trans_eq (sq n)
    omega
  · rw [fastCutScratch_of_lt_seven (by omega)]
    interval_cases n <;> decide

/-- Worst-case `rand`-call budget for executing one `FastCut` subtree of size `k`. -/
def fastCutNodeQueries (k : ℕ) : ℕ :=
  if h : 7 ≤ k then
    have : fastCutThreshold k < k := fastCutThreshold_lt (by omega)
    2 * (k - fastCutThreshold k) + 2 * fastCutNodeQueries (fastCutThreshold k)
  else
    k - 2
termination_by k

/-- Base-case unfolding of `fastCutNodeQueries` for `k < 7`. -/
theorem fastCutNodeQueries_of_lt_seven {k : ℕ} (hk : k < 7) :
    fastCutNodeQueries k = k - 2 := by
  rw [fastCutNodeQueries]
  simp only [show ¬7 ≤ k by omega, ↓reduceDIte]

/-- Recursive unfolding of `fastCutNodeQueries` for `k ≥ 7`. -/
theorem fastCutNodeQueries_of_ge_seven {k : ℕ} (hk : 7 ≤ k) :
    fastCutNodeQueries k =
      2 * (k - fastCutThreshold k) + 2 * fastCutNodeQueries (fastCutThreshold k) := by
  rw [fastCutNodeQueries]
  simp only [hk, ↓reduceDIte]

private theorem fastCutNodeQueries_add_linear_le_pot {k : ℕ} (hk : 7 ≤ k) :
    fastCutNodeQueries k + 4 * (k - 2) ≤ 6 * (k - 4) ^ 2 := by
  fun_induction fastCutNodeQueries k with
  | case1 k h _ ih =>
    have ht6 : 6 ≤ fastCutThreshold k := fastCutThreshold_ge_six h
    by_cases ht7 : 7 ≤ fastCutThreshold k
    · have hih := ih ht7
      have hpot := two_mul_pot_threshold_le h
      have hlin := two_mul_add_two_le_three_mul_threshold h
      omega
    · have ht_eq : fastCutThreshold k = 6 := by omega
      have hbase : fastCutNodeQueries (fastCutThreshold k) = 4 := by
        rw [ht_eq, fastCutNodeQueries_of_lt_seven (by decide)]
      rw [hbase, ht_eq]
      obtain ⟨c, rfl⟩ : ∃ c, k = c + 7 := ⟨k - 7, by omega⟩
      rw [show c + 7 - 6 = c + 1 by omega, show c + 7 - 2 = c + 5 by omega,
        show c + 7 - 4 = c + 3 by omega, show 6 * (c + 3) ^ 2 = 6 * c ^ 2 + 36 * c + 54 by ring]
      omega
  | case2 k h => omega

/-- One `FastCut` tree on `k ≥ 2` vertices makes at most `6 * (k * k)` `rand` calls. -/
theorem fastCutNodeQueries_le {k : ℕ} (hk : 2 ≤ k) :
    fastCutNodeQueries k ≤ 6 * (k * k) := by
  by_cases hk7 : 7 ≤ k
  · have hpot := fastCutNodeQueries_add_linear_le_pot hk7
    have hle := (Nat.pow_le_pow_left (Nat.sub_le k 4) 2).trans_eq (sq k)
    omega
  · rw [fastCutNodeQueries_of_lt_seven (by omega)]
    interval_cases k <;> decide

/-- Worst-case instruction budget for executing a `FastCut` subtree of size `k` inside
`fastCutLoop` (`200 * k ^ 2` internal frame overhead across the 3 stages, `2400` at a base leaf
`k ≤ 6`). -/
def fastCutNodeTime (k : ℕ) : ℕ :=
  if h : 7 ≤ k then
    have : fastCutThreshold k < k := fastCutThreshold_lt (by omega)
    200 * (k * k) + 2 * fastCutNodeTime (fastCutThreshold k)
  else
    2400
termination_by k

/-- Base-case unfolding of `fastCutNodeTime` for `k < 7`. -/
theorem fastCutNodeTime_of_lt_seven {k : ℕ} (hk : k < 7) :
    fastCutNodeTime k = 2400 := by
  rw [fastCutNodeTime]
  simp only [show ¬7 ≤ k by omega, ↓reduceDIte]

/-- Recursive unfolding of `fastCutNodeTime` for `k ≥ 7`. -/
theorem fastCutNodeTime_of_ge_seven {k : ℕ} (hk : 7 ≤ k) :
    fastCutNodeTime k = 200 * (k * k) + 2 * fastCutNodeTime (fastCutThreshold k) := by
  rw [fastCutNodeTime]
  simp only [hk, ↓reduceDIte]

/-- Potential-based upper bound `fastCutNodeTime k ≤ (1200 * fastCutDepth k + 2700) * (k - 4) ^ 2`
for `k ≥ 7`. -/
theorem fastCutNodeTime_le_pot {k : ℕ} (hk : 7 ≤ k) :
    fastCutNodeTime k ≤ (1200 * fastCutDepth k + 2700) * (k - 4) ^ 2 := by
  fun_induction fastCutNodeTime k with
  | case1 k h _ ih =>
    rw [fastCutDepth_of_ge_seven h]
    have hsq : k * k ≤ 6 * (k - 4) ^ 2 := by simpa [sq] using sq_le_six_mul_pot h
    by_cases ht7 : 7 ≤ fastCutThreshold k
    · have hih := ih ht7
      have hpot := two_mul_pot_threshold_le h
      calc 200 * (k * k) + 2 * fastCutNodeTime (fastCutThreshold k)
          ≤ 1200 * (k - 4) ^ 2 +
              2 * ((1200 * fastCutDepth (fastCutThreshold k) + 2700) *
                (fastCutThreshold k - 4) ^ 2) :=
            Nat.add_le_add (by omega) (Nat.mul_le_mul_left 2 hih)
        _ = 1200 * (k - 4) ^ 2 +
              (1200 * fastCutDepth (fastCutThreshold k) + 2700) *
                (2 * (fastCutThreshold k - 4) ^ 2) := by ring
        _ ≤ 1200 * (k - 4) ^ 2 +
              (1200 * fastCutDepth (fastCutThreshold k) + 2700) * (k - 4) ^ 2 := by gcongr
        _ = (1200 * (fastCutDepth (fastCutThreshold k) + 1) + 2700) * (k - 4) ^ 2 := by ring
    · rw [fastCutNodeTime_of_lt_seven (by omega), fastCutDepth_of_lt_seven (by omega)]
      have h9 : 9 ≤ (k - 4) ^ 2 := Nat.pow_le_pow_left (by omega : 3 ≤ k - 4) 2
      omega
  | case2 k h => omega

/-- Closed-form `O(n ^ 2 log n)` bound on `fastCutNodeTime n` for every `n ≥ 2`. -/
theorem fastCutNodeTime_le {n : ℕ} (hn : 2 ≤ n) :
    fastCutNodeTime n ≤ 2400 * n ^ 2 * (Nat.log 2 n + 2) := by
  by_cases hn7 : 7 ≤ n
  · have hpot := fastCutNodeTime_le_pot hn7
    have hd := fastCutDepth_le_two_mul_log n
    have hle : (n - 4) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left (Nat.sub_le n 4) 2
    calc
      fastCutNodeTime n ≤ (1200 * fastCutDepth n + 2700) * (n - 4) ^ 2 := hpot
      _ ≤ (1200 * (2 * Nat.log 2 n) + 4800) * n ^ 2 := by
        apply Nat.mul_le_mul _ hle
        omega
      _ = 2400 * n ^ 2 * (Nat.log 2 n + 2) := by ring
  · rw [fastCutNodeTime_of_lt_seven (by omega)]
    have hn2 : 4 ≤ n ^ 2 := Nat.pow_le_pow_left hn 2
    exact (Nat.mul_le_mul_right _ (by omega : 9600 ≤ 2400 * n ^ 2)).trans'
      (Nat.le_mul_of_pos_right _ (by omega) |>.trans' (by omega))

/-! ### Elementary `ENNReal` probability bounds for Karger–Stein -/

/-- At `k ≥ 7`, contracting down to `t = fastCutThreshold k` preserves a fixed minimum cut with
probability `t * (t - 1) / (k * (k - 1)) ≥ 1 / 2`. -/
theorem half_le_threshold_survival {k : ℕ} (hk : 7 ≤ k) :
    (1 : ℝ≥0∞) / 2 ≤
      ((fastCutThreshold k * (fastCutThreshold k - 1) : ℕ) : ℝ≥0∞) /
        ((k * (k - 1) : ℕ) : ℝ≥0∞) := by
  have hk_ne0 : k * (k - 1) ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  rw [show (1 : ℝ≥0∞) / 2 = ((1 : ℕ) : ℝ≥0∞) / (2 : ℕ) by norm_num,
    ENNReal.natCast_div_le_natCast_div_iff (by decide) hk_ne0, one_mul, Nat.mul_comm _ 2,
    ← Nat.mul_assoc]
  exact fastCutThreshold_spec (by omega)

/-- At a base leaf `2 ≤ k ≤ 6`, a single contraction down to `2` vertices hits a fixed minimum cut
with probability `2 / (k * (k - 1)) ≥ 2 / 30`. -/
theorem base_survival_ge {k : ℕ} (hk2 : 2 ≤ k) (hk6 : k ≤ 6) :
    (2 : ℝ≥0∞) / (30 : ℝ≥0∞) ≤ (2 : ℝ≥0∞) / ((k * (k - 1) : ℕ) : ℝ≥0∞) := by
  apply ENNReal.div_le_div_left
  have hle : k * (k - 1) ≤ 30 := by
    interval_cases k <;> decide
  exact_mod_cast hle

/-- `(1 / 2) * (2 / s) = 1 / s` in `ℝ≥0∞` for `1 ≤ s`. -/
theorem half_mul_two_div_eq {s : ℕ} (hs : 1 ≤ s) :
    ((1 : ℝ≥0∞) / 2) * ((2 : ℝ≥0∞) / (s : ℝ≥0∞)) = (1 : ℝ≥0∞) / (s : ℝ≥0∞) := by
  have _ := hs
  rw [div_eq_mul_inv, div_eq_mul_inv, one_mul, ← mul_assoc,
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul, one_div]

/-- At the root depth budget `d = 2 * Nat.log 2 n`, `2 / (d + 30) = 1 / (Nat.log 2 n + 15)`. -/
theorem root_hit_prob_eq (n : ℕ) :
    (2 : ℝ≥0∞) / ((2 * Nat.log 2 n + 30 : ℕ) : ℝ≥0∞) =
      (1 : ℝ≥0∞) / ((Nat.log 2 n + 15 : ℕ) : ℝ≥0∞) := by
  have hmul : 2 * Nat.log 2 n + 30 = 2 * (Nat.log 2 n + 15) := by omega
  have h20 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2t : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  rw [hmul, Nat.cast_mul, Nat.cast_ofNat]
  simpa using ENNReal.mul_div_mul_left (1 : ℝ≥0∞) ((Nat.log 2 n + 15 : ℕ) : ℝ≥0∞) h20 h2t

/-- Concrete `O(log ^ 2 n)` trial schedule `(Nat.log 2 n + 15) * (Nat.log 2 n + 2)` used by
`fastCutHighProbProgram` to achieve failure probability `≤ 1 / (2 * n)` (instantiating the
asymptotic `O(log ^ 2 n)` repetition count in the proof of `[KargerStein1996]`, Section 4,
Theorem 4.4; paraphrase). -/
def fastCutTrials (n : ℕ) : ℕ :=
  (Nat.log 2 n + 15) * (Nat.log 2 n + 2)

/-- For every `n`, `fastCutTrials n` executes at least one `FastCut` tree
(`1 ≤ fastCutTrials n`). -/
theorem fastCutTrials_pos (n : ℕ) :
    1 ≤ fastCutTrials n :=
  Nat.mul_pos (by omega) (by omega)

/-- Elementary failure probability bound for `fastCutTrials n` independent `FastCut` trees:
`(1 - 1 / (Nat.log 2 n + 15)) ^ fastCutTrials n ≤ 1 / (2 * n)`. -/
theorem fastCutHighProb_failure_le (n : ℕ) :
    ((1 : ℝ≥0∞) - (1 : ℝ≥0∞) / ((Nat.log 2 n + 15 : ℕ) : ℝ≥0∞)) ^ fastCutTrials n ≤
      (1 : ℝ≥0∞) / ((2 * n : ℕ) : ℝ≥0∞) := by
  have hround := ENNReal.one_sub_inv_pow_le_inv_two (k := Nat.log 2 n + 15) (by omega)
  rw [fastCutTrials, pow_mul]
  exact pow_log_two_add_two_le_inv_two_mul (by simpa only [one_div] using hround) n

/-- Weakened failure probability bound `(1 - 1 / (Nat.log 2 n + 15)) ^ fastCutTrials n ≤ 1 / n`. -/
theorem fastCutHighProb_failure_le_inv_n (n : ℕ) :
    ((1 : ℝ≥0∞) - (1 : ℝ≥0∞) / ((Nat.log 2 n + 15 : ℕ) : ℝ≥0∞)) ^ fastCutTrials n ≤
      (1 : ℝ≥0∞) / (n : ℝ≥0∞) := by
  refine (fastCutHighProb_failure_le n).trans ?_
  apply ENNReal.div_le_div_left
  exact_mod_cast (by omega : n ≤ 2 * n)

end Cslib.Algorithms.Karger
