/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.WeightedCut.Contraction
public import CslibFrontier.Probability.PMF.Event
public import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Nat.Log
import CslibFrontier.Foundations.Analysis.ENNRealNatDiv
import CslibFrontier.Foundations.Analysis.ENNRealOneSubInvPow
import CslibFrontier.Foundations.Data.Nat.Choose

/-!
# Supervertex contractions and Karger's survival bounds

Combinatorial and probabilistic core for Karger's randomized contraction algorithm `[Karger1993]`
and the Karger–Stein recursive algorithm `[KargerStein1996]` on `n`-vertex weighted undirected
multigraphs represented as symmetric zero-diagonal adjacency matrices `W : Fin n → Fin n → ℕ`.
Multigraphs, cut weights, global minimum cuts and contractions along supervertex maps are the
general notions of `CslibFrontier.Foundations.Combinatorics.WeightedCut` (`Cslib.WeightedCut`), and
the swap-compacted contraction of one pair of supervertices (`mergePair`, `embedCompact`,
`contractMatrix`, `contractPart`) is
`CslibFrontier.Foundations.Combinatorics.WeightedCut.Contraction`;
this module adds edge-weight-proportional sampling and the survival bounds. Nothing here refers to
a machine: the word-RAM programs (`CslibFrontier.Algorithms.WordRAM.Karger.Contract`,
`CslibFrontier.Algorithms.WordRAM.KargerMinCut`) store the matrix in row-major order
(`Cslib.Algorithms.WordRAM.Karger.flattenMatrix`) and import these facts.

## Source statements and notation mapping

* **Cut-survival bounds (paraphrase):**
  - `[Karger1993]`, Section 2, Theorem 2.1 and Corollary 2.1 (paraphrase): contracting randomly
    chosen edges in an `n`-vertex multigraph down to `2` meta-vertices preserves any fixed global
    minimum cut with probability at least `C(n, 2)⁻¹ = 2 / (n * (n - 1))`, and repeating
    `O(n ^ 2 log n)` independent trials finds a minimum cut with high probability.
  - `[KargerStein1996]`, Section 2, Lemma 2.1, Theorem 2.2, and Corollary 2.3, and Section 2.1,
    Corollary 2.4 (paraphrase): a fixed cut survives contraction if and only if no contracted edge
    crosses it; at `k` active supervertices every singleton cut has weight at least `minCut W`, so
    total doubled weight `S` is at least `k * minCut W`, a single edge-weight-proportional step
    crosses a fixed minimum cut with probability at most `2 / k`, and contracting from `n` down to
    `t` supervertices preserves the cut with probability at least
    `C(t, 2) / C(n, 2) = t * (t - 1) / (n * (n - 1))`.
  - `[MitzenmacherUpfal2017]`, Section 1.5, Theorem 1.8 (paraphrase): multiplying the conditional
    single-step survival bounds `1 - 2 / i = (i - 2) / i` for `i = n, …, 3` telescopes to
    `2 / (n * (n - 1))`.
* **Notation mapping and implementation variants:**
  - `C(t, 2) / C(n, 2)` and `C(n, 2)⁻¹` ↔ `((t * (t - 1) : ℕ) : ℝ≥0∞) / (n * (n - 1))` and
    `2 / (n * (n - 1))` (`step_survival_prob_ge`, `telescope_survival_step`);
  - `[KargerStein1996]`, Section 3.1, Lemma 3.1 selects `(u, v)` with probability
    `2 * W u v / S` via two `Random-Select` draws (`u` proportional to `D(u)` then `v` proportional
    to `W(u, v)`); our `edgeOffset` / `IsSampledPair` formalizes an equivalent single-draw variant
    using one uniform draw `r ∈ Fin S` (`S = totalDoubledWeight W = ∑ u, rowDeg W u`) resolved by
    prefix sums over `rowDeg` then row weights `W u v`, achieving the same `2 * W u v / S`
    distribution;
  - `[KargerStein1996]`, Section 3.2 (Figure 5) updates the `n × n` matrix in `O(n)` time per
    contraction (hence Corollary 3.2's `O(n ^ 2)` total); our `embedCompact` / `contractMatrix`
    swap-compacts active slot `k - 1` into the removed slot `v` so each contraction on `k` active
    supervertices scans only `0..k - 1` (`O(k)` time);
  - `highProbTrials n = (n * (n - 1) / 2) * (Nat.log 2 n + 2)` and the elementary `Real.exp`-free
    Bernoulli bound `highProb_failure_le` (`≤ 1 / (2 * n)`) are our own concrete parameter choices
    instantiating the `O(n ^ 2 log n)` repeated-trial amplification of `[Karger1993]`, Section 2,
    Corollary 2.1.

## Main definitions

* `Cslib.Algorithms.Karger.edgeOffset`, `Cslib.Algorithms.Karger.IsSampledPair`:
  prefix-sum interval characterization of edge-weight-proportional sampling from `Fin S`.

## Main results

* `Cslib.Algorithms.Karger.surviving_card_eq`,
  `Cslib.Algorithms.Karger.step_survival_prob_ge`: a fixed minimum cut survives one
  edge-proportional contraction on `k` supervertices with probability at least `(k - 2) / k`.
* `Cslib.Algorithms.Karger.telescope_survival_step`: telescoping multiplication identity
  `((m - 1) / (m + 1)) * (t * (t - 1) / (m * (m - 1))) = t * (t - 1) / ((m + 1) * m)` in `ℝ≥0∞`.
* `Cslib.Algorithms.Karger.pow_log_two_add_two_le_inv_two_mul`: `Nat.log 2 n + 2` repetitions of a
  round that fails with probability at most `1 / 2` all fail with probability at most `1 / (2 * n)`.
* `Cslib.Algorithms.Karger.highProb_failure_le`: elementary Bernoulli amplification bound
  `(1 - 2 / (n * (n - 1))) ^ ((n * (n - 1) / 2) * (Nat.log 2 n + 2)) ≤ 1 / (2 * n)`.

## References

* [D. R. Karger, *Global Min-cuts in RNC, and Other Ramifications of a Simple Min-Cut
  Algorithm*][Karger1993]
* [D. R. Karger and C. Stein, *A New Approach to the Minimum Cut Problem*][KargerStein1996]
* [M. Mitzenmacher and E. Upfal, *Probability and Computing*][MitzenmacherUpfal2017]
-/

@[expose] public section

namespace Cslib.Algorithms.Karger

open scoped ENNReal
open Cslib.WeightedCut

/-! ### Prefix-sum edge-proportional sampling on `Fin S` -/

/-- Sum of `rowDeg W a` over all `a < u`. -/
def degBefore {k : ℕ} (W : Fin k → Fin k → ℕ) (u : Fin k) : ℕ :=
  ∑ a ∈ Finset.univ.filter (· < u), rowDeg W a

/-- Sum of `W u b` over all `b < v`. -/
def weightBefore {k : ℕ} (W : Fin k → Fin k → ℕ) (u v : Fin k) : ℕ :=
  ∑ b ∈ Finset.univ.filter (· < v), W u b

/-- Flattened prefix-sum start offset of directed edge slot `(u, v)` inside `[0, S)`. -/
def edgeOffset {k : ℕ} (W : Fin k → Fin k → ℕ) (u v : Fin k) : ℕ :=
  degBefore W u + weightBefore W u v

/-! `degBefore` and `weightBefore` are both sums of some `f : Fin k → ℕ` over the indices below a
cutoff. The three facts below about such prefix sums serve both of them. -/

/-- Adding the cutoff's own term to a prefix sum stays below any later prefix sum. -/
private theorem sum_lt_add_le_of_lt {k : ℕ} (f : Fin k → ℕ) {u₁ u₂ : Fin k} (hlt : u₁ < u₂) :
    (∑ a ∈ Finset.univ.filter (· < u₁), f a) + f u₁ ≤ ∑ a ∈ Finset.univ.filter (· < u₂), f a := by
  rw [add_comm, ← Finset.sum_insert (by simp)]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun a ha => ?_) fun _ _ _ => Nat.zero_le _
  simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
  exact ha.elim (· ▸ hlt) (·.trans hlt)

/-- Adding the cutoff's own term to a prefix sum stays below the total. -/
private theorem sum_lt_add_le_sum {k : ℕ} (f : Fin k → ℕ) (u : Fin k) :
    (∑ a ∈ Finset.univ.filter (· < u), f a) + f u ≤ ∑ a, f a := by
  rw [add_comm, ← Finset.sum_insert (by simp)]
  exact Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _

/-- Every value below the total lies in the block `[prefix, prefix + f u)` of some index `u`. -/
private theorem exists_sum_lt_le_lt {k : ℕ} (f : Fin k → ℕ) {r : ℕ} (hr : r < ∑ a, f a) :
    ∃ u : Fin k, (∑ a ∈ Finset.univ.filter (· < u), f a) ≤ r ∧
      r < (∑ a ∈ Finset.univ.filter (· < u), f a) + f u := by
  obtain ⟨⟨u, j⟩, hj⟩ := finSigmaFinEquiv.surjective (⟨r, hr⟩ : Fin (∑ a, f a))
  have hval := finSigmaFinEquiv_apply (n := f) ⟨u, j⟩
  have hprefix : ∑ i : Fin u.val, f (Fin.castLE u.2.le i) =
      ∑ a ∈ Finset.univ.filter (· < u), f a :=
    Finset.sum_bij (fun i _ => Fin.castLE u.2.le i)
      (fun i _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.isLt⟩)
      (fun _ _ _ _ h => Fin.castLE_injective _ h)
      (fun a ha => ⟨⟨a.val, (Finset.mem_filter.mp ha).2⟩, Finset.mem_univ _, rfl⟩) fun _ _ => rfl
  rw [hj, hprefix] at hval
  dsimp only at hval
  exact ⟨u, by omega, by omega⟩

theorem weightBefore_add_le_rowDeg {k : ℕ} (W : Fin k → Fin k → ℕ) (u v : Fin k) :
    weightBefore W u v + W u v ≤ rowDeg W u :=
  sum_lt_add_le_sum (W u) v

theorem weightBefore_le_of_lt {k : ℕ} (W : Fin k → Fin k → ℕ) (u : Fin k)
    {v₁ v₂ : Fin k} (hlt : v₁ < v₂) :
    weightBefore W u v₁ + W u v₁ ≤ weightBefore W u v₂ :=
  sum_lt_add_le_of_lt (W u) hlt

theorem degBefore_add_le_totalDoubledWeight {k : ℕ} (W : Fin k → Fin k → ℕ) (u : Fin k) :
    degBefore W u + rowDeg W u ≤ totalDoubledWeight W :=
  sum_lt_add_le_sum (rowDeg W) u

theorem degBefore_le_of_lt {k : ℕ} (W : Fin k → Fin k → ℕ) {u₁ u₂ : Fin k} (hlt : u₁ < u₂) :
    degBefore W u₁ + rowDeg W u₁ ≤ degBefore W u₂ :=
  sum_lt_add_le_of_lt (rowDeg W) hlt

theorem edgeOffset_add_le_totalDoubledWeight {k : ℕ} (W : Fin k → Fin k → ℕ) (u v : Fin k) :
    edgeOffset W u v + W u v ≤ totalDoubledWeight W := by
  unfold edgeOffset
  have := weightBefore_add_le_rowDeg W u v
  have := degBefore_add_le_totalDoubledWeight W u
  omega

/-- `IsSampledPair W r u v` holds when sample `r` falls inside the half-open interval
`[edgeOffset W u v, edgeOffset W u v + W u v)`. -/
def IsSampledPair {k : ℕ} (W : Fin k → Fin k → ℕ) (r : ℕ) (u v : Fin k) : Prop :=
  edgeOffset W u v ≤ r ∧ r < edgeOffset W u v + W u v

instance {k : ℕ} (W : Fin k → Fin k → ℕ) (r : ℕ) (u v : Fin k) :
    Decidable (IsSampledPair W r u v) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem isSampledPair_ne {k : ℕ} {W : Fin k → Fin k → ℕ} (hW : IsMultigraph W)
    {r : ℕ} {u v : Fin k} (h : IsSampledPair W r u v) :
    u ≠ v := by
  rintro rfl
  rcases h with ⟨hle, hlt⟩
  rw [hW.2 u] at hlt
  omega

theorem isSampledPair_unique {k : ℕ} (W : Fin k → Fin k → ℕ) {r : ℕ}
    {u₁ v₁ u₂ v₂ : Fin k} (h₁ : IsSampledPair W r u₁ v₁) (h₂ : IsSampledPair W r u₂ v₂) :
    u₁ = u₂ ∧ v₁ = v₂ := by
  rcases h₁ with ⟨hle₁, hlt₁⟩
  rcases h₂ with ⟨hle₂, hlt₂⟩
  unfold edgeOffset at hle₁ hlt₁ hle₂ hlt₂
  have hu₁_upper : r < degBefore W u₁ + rowDeg W u₁ := by
    have := weightBefore_add_le_rowDeg W u₁ v₁
    omega
  have hu₂_upper : r < degBefore W u₂ + rowDeg W u₂ := by
    have := weightBefore_add_le_rowDeg W u₂ v₂
    omega
  have hu_eq : u₁ = u₂ := by
    rcases lt_trichotomy u₁ u₂ with hlt | rfl | hgt
    · have := degBefore_le_of_lt W hlt
      omega
    · rfl
    · have := degBefore_le_of_lt W hgt
      omega
  subst hu_eq
  refine ⟨rfl, ?_⟩
  rcases lt_trichotomy v₁ v₂ with hlt | rfl | hgt
  · have := weightBefore_le_of_lt W u₁ hlt
    omega
  · rfl
  · have := weightBefore_le_of_lt W u₁ hgt
    omega

theorem exists_isSampledPair {k : ℕ} (W : Fin k → Fin k → ℕ) {r : ℕ}
    (hr : r < totalDoubledWeight W) :
    ∃ u v : Fin k, IsSampledPair W r u v := by
  obtain ⟨u, hu_le, hu_lt⟩ := exists_sum_lt_le_lt (rowDeg W) hr
  obtain ⟨v, hv_le, hv_lt⟩ := exists_sum_lt_le_lt (W u) (r := r - degBefore W u)
    (by unfold degBefore rowDeg at *; omega)
  exact ⟨u, v, by unfold IsSampledPair edgeOffset degBefore weightBefore at *; omega⟩

theorem card_sampledPair_fiber {k : ℕ} (W : Fin k → Fin k → ℕ) (u v : Fin k) :
    (Finset.univ.filter fun r : Fin (totalDoubledWeight W) =>
      IsSampledPair W r.val u v).card = W u v := by
  have hbound := edgeOffset_add_le_totalDoubledWeight W u v
  symm
  rw [← Finset.card_fin (W u v)]
  refine Finset.card_bij (fun (i : Fin (W u v)) _ =>
    (⟨edgeOffset W u v + i.val, by omega⟩ : Fin (totalDoubledWeight W)))
    (fun i _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp only [IsSampledPair]; omega⟩)
    (fun i _ j _ hij => Fin.ext (by simp only [Fin.ext_iff] at hij; omega)) fun r hr => ?_
  rcases (Finset.mem_filter.mp hr).2 with ⟨hr1, hr2⟩
  refine ⟨⟨r.val - edgeOffset W u v, by omega⟩, Finset.mem_univ _, Fin.ext ?_⟩
  dsimp
  omega

/-- Event on `Fin (totalDoubledWeight W)` where the edge sampled at `r` keeps both endpoints on the
same side of `B`. -/
def SampleSurvives {k : ℕ} (W : Fin k → Fin k → ℕ) (B : Finset (Fin k))
    (r : Fin (totalDoubledWeight W)) : Prop :=
  ∃ u v : Fin k, IsSampledPair W r.val u v ∧ (u ∈ B ↔ v ∈ B)

instance {k : ℕ} (W : Fin k → Fin k → ℕ) (B : Finset (Fin k))
    (r : Fin (totalDoubledWeight W)) :
    Decidable (SampleSurvives W B r) :=
  inferInstanceAs (Decidable (∃ _ _, _))

theorem not_sampleSurvives_iff_crosses {k : ℕ} (W : Fin k → Fin k → ℕ) (B : Finset (Fin k))
    (r : Fin (totalDoubledWeight W)) :
    ¬ SampleSurvives W B r ↔
      ∃ u v : Fin k, IsSampledPair W r.val u v ∧ ¬ (u ∈ B ↔ v ∈ B) := by
  rcases exists_isSampledPair W r.isLt with ⟨u₀, v₀, h₀⟩
  constructor
  · intro hns
    exact ⟨u₀, v₀, h₀, fun hiff => hns ⟨u₀, v₀, h₀, hiff⟩⟩
  · rintro ⟨u, v, huv, hnc⟩ ⟨u', v', huv', hiff⟩
    rcases isSampledPair_unique W huv huv' with ⟨rfl, rfl⟩
    exact hnc hiff

theorem crossing_card_eq {k : ℕ} {W : Fin k → Fin k → ℕ} (hW : IsMultigraph W)
    (B : Finset (Fin k)) :
    (Finset.univ.filter fun r : Fin (totalDoubledWeight W) => ¬ SampleSurvives W B r).card =
      2 * cutWeight W B := by
  let crossPairs : Finset (Fin k × Fin k) :=
    Finset.univ.filter fun p => ¬ (p.1 ∈ B ↔ p.2 ∈ B)
  have hbiUnion : (Finset.univ.filter fun r : Fin (totalDoubledWeight W) =>
      ¬ SampleSurvives W B r) =
        crossPairs.biUnion fun p =>
          Finset.univ.filter fun r : Fin (totalDoubledWeight W) =>
            IsSampledPair W r.val p.1 p.2 := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_sampleSurvives_iff_crosses,
      Finset.mem_biUnion, Prod.exists, crossPairs]
    exact ⟨fun ⟨u, v, huv, hnc⟩ => ⟨u, v, hnc, huv⟩,
      fun ⟨u, v, hnc, huv⟩ => ⟨u, v, huv, hnc⟩⟩
  rw [hbiUnion, Finset.card_biUnion]
  · calc
      ∑ p ∈ crossPairs,
          (Finset.univ.filter fun r : Fin (totalDoubledWeight W) =>
            IsSampledPair W r.val p.1 p.2).card
        = ∑ p ∈ crossPairs, W p.1 p.2 :=
          Finset.sum_congr rfl fun p _ => card_sampledPair_fiber W p.1 p.2
      _ = (∑ p ∈ B ×ˢ (Finset.univ \ B), W p.1 p.2) +
            ∑ p ∈ (Finset.univ \ B) ×ˢ B, W p.1 p.2 := by
          rw [← Finset.sum_union]
          · refine Finset.sum_congr ?_ fun _ _ => rfl
            ext ⟨u, v⟩
            simp only [crossPairs, Finset.mem_filter, Finset.mem_univ, true_and,
              Finset.mem_union, Finset.mem_product, Finset.mem_sdiff]
            tauto
          · simp only [Finset.disjoint_left, Finset.mem_product, Finset.mem_sdiff, Finset.mem_univ,
              true_and]
            rintro ⟨u, v⟩ ⟨hu, _⟩ ⟨hnu, _⟩
            exact hnu hu
      _ = cutWeight W B + cutWeight W (Finset.univ \ B) := by
          have hsdiff : Finset.univ \ (Finset.univ \ B) = B := by ext x; simp
          unfold cutWeight
          rw [hsdiff, Finset.sum_product, Finset.sum_product]
      _ = 2 * cutWeight W B := by
          rw [cutWeight_compl hW B]
          ring
  · intro p₁ _ p₂ _ hpne
    simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and]
    intro r h₁ h₂
    rcases isSampledPair_unique W h₁ h₂ with ⟨hu, hv⟩
    exact hpne (Prod.ext hu hv)

theorem surviving_card_eq {k : ℕ} {W : Fin k → Fin k → ℕ} (hW : IsMultigraph W)
    (B : Finset (Fin k)) :
    (Finset.univ.filter fun r : Fin (totalDoubledWeight W) => SampleSurvives W B r).card =
      totalDoubledWeight W - 2 * cutWeight W B := by
  have hpart := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (totalDoubledWeight W)))) (fun r => SampleSurvives W B r)
  rw [Finset.card_univ, Fintype.card_fin, crossing_card_eq hW B] at hpart
  have := two_mul_cutWeight_le_totalDoubledWeight hW B
  omega

/-- One-step survival probability lower bound: if `k ≥ 2`, `0 < totalDoubledWeight W`, and
`k * cutWeight W B ≤ totalDoubledWeight W`, then a uniform sample `r : Fin (totalDoubledWeight W)`
satisfies `SampleSurvives W B r` with probability at least `(k - 2) / k`. -/
theorem step_survival_prob_ge {k : ℕ} (hk : 2 ≤ k) {W : Fin k → Fin k → ℕ} (hW : IsMultigraph W)
    {B : Finset (Fin k)} (hS : 0 < totalDoubledWeight W)
    (hdeg : k * cutWeight W B ≤ totalDoubledWeight W) :
    ((k - 2 : ℕ) : ℝ≥0∞) / k ≤
      letI : Nonempty (Fin (totalDoubledWeight W)) := ⟨⟨0, hS⟩⟩
      (Cslib.Probability.PMF.uniformOfFintype (Fin (totalDoubledWeight W))).toOuterMeasure
        {r | SampleSurvives W B r} := by
  let S := totalDoubledWeight W
  let _ : Nonempty (Fin S) := ⟨⟨0, hS⟩⟩
  rw [Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype]
  have hcard :
      (Finset.univ.filter (· ∈ ({r : Fin S | SampleSurvives W B r} : Set (Fin S)))).card =
        S - 2 * cutWeight W B := surviving_card_eq hW B
  rw [hcard, Fintype.card_fin, ← div_eq_mul_inv]
  have hnat : (k - 2) * S ≤ k * (S - 2 * cutWeight W B) := by
    have h2 : 2 * cutWeight W B ≤ S := by
      have : 2 * cutWeight W B ≤ k * cutWeight W B := Nat.mul_le_mul_right _ hk
      omega
    zify [hk, h2]
    nlinarith
  exact (ENNReal.natCast_div_le_natCast_div_iff (by omega) hS.ne').mpr
    (hnat.trans_eq (Nat.mul_comm _ _))

/-! ### Telescoping and Bernoulli amplification -/

private theorem two_le_mul_pred {n : ℕ} (hn : 2 ≤ n) : 2 ≤ n * (n - 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 2 := ⟨n - 2, by omega⟩
  have hsub : d + 2 - 1 = d + 1 := by omega
  rw [hsub]
  nlinarith

/-- Telescoping cancellation step for `contractDownTo` survival probability from `m + 1` down to
`t` (`2 ≤ t ≤ m`):
`((m - 1) / (m + 1)) * (t * (t - 1) / (m * (m - 1))) = t * (t - 1) / ((m + 1) * m)`. -/
theorem telescope_survival_step {t m : ℕ} (ht : 2 ≤ t) (htm : t ≤ m) :
    (((m - 1 : ℕ) : ℝ≥0∞) / (m + 1 : ℕ)) *
      (((t * (t - 1) : ℕ) : ℝ≥0∞) / ((m * (m - 1) : ℕ) : ℝ≥0∞)) =
      ((t * (t - 1) : ℕ) : ℝ≥0∞) / (((m + 1) * m : ℕ) : ℝ≥0∞) := by
  have hm1_pos : 0 < m - 1 := by omega
  have hm_pos : 0 < m := by omega
  have hmp1_ne0 : ((m + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by positivity
  have hmp1_top : ((m + 1 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hmm1_ne0 : ((m * (m - 1) : ℕ) : ℝ≥0∞) ≠ 0 := mod_cast (Nat.mul_pos hm_pos hm1_pos).ne'
  have hmp1m_ne0 : (((m + 1) * m : ℕ) : ℝ≥0∞) ≠ 0 :=
    mod_cast (Nat.mul_pos (Nat.succ_pos m) hm_pos).ne'
  have hprod : (((m - 1 : ℕ) : ℝ≥0∞) / (m + 1 : ℕ)) *
      (((t * (t - 1) : ℕ) : ℝ≥0∞) / ((m * (m - 1) : ℕ) : ℝ≥0∞)) =
      (((m - 1 : ℕ) : ℝ≥0∞) * ((t * (t - 1) : ℕ) : ℝ≥0∞)) /
        (((m + 1 : ℕ) : ℝ≥0∞) * ((m * (m - 1) : ℕ) : ℝ≥0∞)) := by
    simp only [div_eq_mul_inv, ENNReal.mul_inv (Or.inl hmp1_ne0) (Or.inl hmp1_top)]
    ring
  rw [hprod, ENNReal.div_eq_div_iff hmp1m_ne0 (ENNReal.natCast_ne_top _)
    (mul_ne_zero hmp1_ne0 hmm1_ne0) (ENNReal.mul_ne_top hmp1_top (ENNReal.natCast_ne_top _))]
  exact_mod_cast (by ring :
    ((m + 1) * m) * ((m - 1) * (t * (t - 1))) = ((m + 1) * (m * (m - 1))) * (t * (t - 1)))

theorem one_sub_two_div_pairs_eq {n : ℕ} (hn : 2 ≤ n) :
    (1 : ℝ≥0∞) - (2 : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞) =
      (((n * (n - 1) / 2 - 1 : ℕ) : ℝ≥0∞) / ((n * (n - 1) / 2 : ℕ) : ℝ≥0∞)) := by
  let m := n * (n - 1) / 2
  have heven : 2 ∣ n * (n - 1) := by
    rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · refine ⟨k * (2 * k - 1), ?_⟩
      have : (k + k) * (k + k - 1) = 2 * (k * (2 * k - 1)) := by
        rcases k with _ | k'
        · simp
        · have h1 : k' + 1 + (k' + 1) - 1 = 2 * k' + 1 := by omega
          have h2 : 2 * (k' + 1) - 1 = 2 * k' + 1 := by omega
          rw [h1, h2]
          ring
      exact this
    · refine ⟨(2 * k + 1) * k, ?_⟩
      have : 2 * k + 1 - 1 = 2 * k := by omega
      rw [this]
      ring
  have h2m : n * (n - 1) = 2 * m := (Nat.mul_div_cancel' heven).symm
  have hm_pos : 1 ≤ m := by
    have := two_le_mul_pred hn
    omega
  have hm_ne0 : (m : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hm_top : (m : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top m
  have h2_ne0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2_top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have h2n_ne0 : ((n * (n - 1) : ℕ) : ℝ≥0∞) ≠ 0 := by
    have := two_le_mul_pred hn
    exact_mod_cast (by omega : n * (n - 1) ≠ 0)
  refine ENNReal.sub_eq_of_eq_add (ENNReal.div_ne_top h2_top h2n_ne0) ?_
  change (1 : ℝ≥0∞) = (((m - 1 : ℕ) : ℝ≥0∞) / (m : ℝ≥0∞)) +
    (2 : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞)
  rw [h2m, Nat.cast_mul, Nat.cast_ofNat]
  have hdiv2 : (2 : ℝ≥0∞) / ((2 : ℝ≥0∞) * (m : ℝ≥0∞)) = (1 : ℝ≥0∞) / (m : ℝ≥0∞) := by
    simpa using ENNReal.mul_div_mul_left (1 : ℝ≥0∞) (m : ℝ≥0∞) h2_ne0 h2_top
  rw [hdiv2, div_eq_mul_inv, div_eq_mul_inv, ← add_mul]
  have hsub : ((m - 1 : ℕ) : ℝ≥0∞) + 1 = (m : ℝ≥0∞) := by
    exact_mod_cast Nat.sub_add_cancel hm_pos
  rw [hsub, ← div_eq_mul_inv, ENNReal.div_self hm_ne0 hm_top]

theorem one_sub_two_div_pow_pairs_le_half {n : ℕ} (hn : 2 ≤ n) :
    ((1 : ℝ≥0∞) - (2 : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞)) ^ (n * (n - 1) / 2) ≤
      (1 : ℝ≥0∞) / 2 := by
  rw [one_sub_two_div_pairs_eq hn]
  exact ENNReal.natCast_pred_div_pow_le_half (by have := two_le_mul_pred hn; omega)

/-- Elementary high-probability trial count `(n * (n - 1) / 2) * (Nat.log 2 n + 2)` for Basic
Karger amplification. -/
def highProbTrials (n : ℕ) : ℕ :=
  (n * (n - 1) / 2) * (Nat.log 2 n + 2)

theorem highProbTrials_pos {n : ℕ} (hn : 2 ≤ n) :
    1 ≤ highProbTrials n := by
  unfold highProbTrials
  have hm : 1 ≤ n * (n - 1) / 2 := by
    have := two_le_mul_pred hn
    omega
  nlinarith

/-- Amplification by `Nat.log 2 n + 2` independent repetitions: if one round fails with
probability at most `1 / 2`, all rounds fail with probability at most `1 / (2 * n)`. -/
theorem pow_log_two_add_two_le_inv_two_mul {p : ℝ≥0∞} (hp : p ≤ 1 / 2) (n : ℕ) :
    p ^ (Nat.log 2 n + 2) ≤ (1 : ℝ≥0∞) / ((2 * n : ℕ) : ℝ≥0∞) := by
  refine (pow_le_pow_left' hp _).trans ?_
  rw [ENNReal.div_pow, one_pow]
  apply ENNReal.div_le_div_left
  have hlt : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by omega) n
  have hle : 2 * n ≤ 2 ^ (Nat.log 2 n + 2) := by
    rw [pow_succ']
    omega
  exact_mod_cast hle

/-- Elementary failure probability bound for `highProbTrials n` independent contractions:
`(1 - 2 / (n * (n - 1))) ^ ((n * (n - 1) / 2) * (Nat.log 2 n + 2)) ≤ 1 / (2 * n)`. -/
theorem highProb_failure_le {n : ℕ} (hn : 2 ≤ n) :
    ((1 : ℝ≥0∞) - (2 : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞)) ^ highProbTrials n ≤
      (1 : ℝ≥0∞) / ((2 * n : ℕ) : ℝ≥0∞) := by
  rw [highProbTrials, pow_mul]
  exact pow_log_two_add_two_le_inv_two_mul (one_sub_two_div_pow_pairs_le_half hn) n

theorem highProb_failure_le_inv_n {n : ℕ} (hn : 2 ≤ n) :
    ((1 : ℝ≥0∞) - (2 : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞)) ^ highProbTrials n ≤
      (1 : ℝ≥0∞) / (n : ℝ≥0∞) := by
  refine (highProb_failure_le hn).trans ?_
  apply ENNReal.div_le_div_left
  exact_mod_cast (by omega : n ≤ 2 * n)

end Cslib.Algorithms.Karger
