/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/Cheeger.lean`)

public import CslibFrontier.Init
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Combinatorics.SimpleGraph.Density
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The normalized graph Laplacian and discrete Cheeger inequalities

For a finite simple graph `G : SimpleGraph V` (not necessarily regular), this module formalizes
Fan Chung's normalized Laplacian `𝓛_G = T^{-1/2} L T^{-1/2}`, vertex-set volume `vol(S)`,
conductance (Cheeger constant) `h_G`, spectral gap `λ_G = λ_1`, explicit sweep-cut rounding, and
both the general-degree normalized Cheeger inequality ([Chung1997], Chapters 1–2) and the
combinatorial-Laplacian Cheeger inequality ([Chung1997], §2.5; [AlonMilman1985]):

1. **Normalized Laplacian and Rayleigh quotient** ([Chung1997], §1.2, pp. 2–5):
   * `SimpleGraph.degInvSqrtMatrix` (`T^{-1/2}`, with convention `T^{-1}(v, v) = 0` at isolated
     vertices `d_v = 0`) and `SimpleGraph.normLapMatrix` (`𝓛_G = T^{-1/2} L T^{-1/2}`), proved
     symmetric and positive semidefinite with kernel vector `v ↦ √(d_v)` and quadratic form
     `f ⬝ᵥ (L *ᵥ f) = (1 / 2) ∑_{u, v : G.Adj u v} (f u - f v)²`.
   * `SimpleGraph.normSpectralGap` (`λ_G`, [Chung1997], Eq. (1.2), p. 4): infimum of
     `SimpleGraph.normRayleigh` over `f : V → ℝ` with `∑ v, f v * d_v = 0` and
     `0 < ∑ v, f v ^ 2 * d_v` (`0` on edgeless graphs `G = ⊥`; equal to the second eigenvalue
     `λ_1` of `SimpleGraph.normLapMatrix` when `G` has no isolated vertices, whereas isolated
     vertices contribute extra `0` eigenvalues to `normLapMatrix` while `normRayleigh` ignores
     `d_v = 0` coordinates), satisfying `0 ≤ λ_G ≤ 2`, `λ_{K_n} = n / (n - 1)` for `2 ≤ n`
     (Example 1.1, p. 6), and `λ_G ≤ 1` when two positive-degree vertices are nonadjacent
     (Lemma 1.7(iii), p. 7).
2. **Conductance, sweep-cut rounding, and normalized Cheeger inequality** ([Chung1997], §§2.2–2.3,
   pp. 24–28):
   * `SimpleGraph.vol`, `SimpleGraph.totalVol`, `SimpleGraph.setConductance` (`h_G(S)` in Eq. (2.1),
     p. 24), and `SimpleGraph.conductance` (`h_G` in Eq. (2.2), p. 24).
   * **Upper bound** (`SimpleGraph.normSpectralGap_le_two_mul_conductance`, Lemma 2.1, p. 25):
     `λ_G ≤ 2 h_G`.
   * **Sweep-cut rounding** (`SimpleGraph.exists_sweep_cut_le`, proof of Theorems 2.2–2.3,
     pp. 26–28): for every `f` with `∑ v, f v * d_v = 0` and `0 < ∑ v, f v ^ 2 * d_v`, there is an
     explicit threshold cut `S` (`0 < vol S ≤ vol(G) / 2`) satisfying
     `1 - √(1 - h_G(S)²) ≤ R_G(f)` and `h_G(S) ≤ √(2 R_G(f))`.
   * **Lower bounds** (`SimpleGraph.one_sub_sqrt_one_sub_conductance_sq_le_normSpectralGap`,
     Theorem 2.3, p. 27; `SimpleGraph.conductance_sq_div_two_le_normSpectralGap` and
     `SimpleGraph.conductance_sq_div_two_lt_normSpectralGap`, Theorem 2.2, p. 26):
     `h_G² / 2 ≤ 1 - √(1 - h_G²) ≤ λ_G`, with strict inequality `h_G² / 2 < λ_G` whenever
     `0 < h_G` (in particular for every connected graph on at least two vertices).
3. **Combinatorial Laplacian / Fiedler algebraic connectivity** ([Chung1997], §2.5, pp. 34–35;
   [AlonMilman1985]):
   * `SimpleGraph.isoperimetricNum` (`h'_G`) and `SimpleGraph.algConnectivity` (`λ'_1`), with
     `λ'_1 ≤ 2 h'_G` (`algConnectivity_le_two_mul_isoperimetricNum`), explicit cardinality
     sweep-cut rounding (`exists_card_sweep_cut_le`), and `(h'_G)² ≤ 2 Δ λ'_1`
     (`isoperimetricNum_sq_le_two_mul_maxDegree_mul_algConnectivity`).

For port-labeled `d`-regular multigraphs (`Cslib.RotationMap`), see
`CslibFrontier.Foundations.Combinatorics.Expander.Cheeger`.

## Main definitions

* `SimpleGraph.vol`, `SimpleGraph.totalVol`: degree-sum volume of a vertex set and of the graph.
* `SimpleGraph.setConductance`, `SimpleGraph.conductance`: cut conductance `h_G(S)` and Cheeger
  constant `h_G`.
* `SimpleGraph.degInvSqrtMatrix`, `SimpleGraph.normLapMatrix`: inverse-square-root degree matrix
  `T^{-1/2}` and normalized Laplacian `𝓛_G = T^{-1/2} L T^{-1/2}`.
* `SimpleGraph.normRayleigh`, `SimpleGraph.normSpectralGap`: normalized Rayleigh quotient and
  spectral gap `λ_G = λ_1`.
* `SimpleGraph.isoperimetricNum`, `SimpleGraph.algConnectivity`: vertex-cardinality isoperimetric
  number `h'_G` and combinatorial-Laplacian algebraic connectivity `λ'_1`.

## Main results

* `SimpleGraph.normLapMatrix_apply`, `SimpleGraph.isSymm_normLapMatrix`,
  `SimpleGraph.posSemidef_normLapMatrix`, `SimpleGraph.normLapMatrix_mulVec_sqrt_degree`:
  matrix properties of `𝓛_G`.
* `SimpleGraph.normSpectralGap_top`, `SimpleGraph.normSpectralGap_le_two`,
  `SimpleGraph.normSpectralGap_le_one_of_ne_top`: exact `K_n` value and general upper bounds.
* `SimpleGraph.normSpectralGap_le_two_mul_conductance`: easy half `λ_G ≤ 2 h_G`
  ([Chung1997], Lemma 2.1).
* `SimpleGraph.exists_sweep_cut_le`: explicit threshold sweep-cut rounding for any vector
  orthogonal to degrees.
* `SimpleGraph.one_sub_sqrt_one_sub_conductance_sq_le_normSpectralGap`: strengthened Cheeger lower
  bound `1 - √(1 - h_G²) ≤ λ_G` ([Chung1997], Theorem 2.3).
* `SimpleGraph.conductance_sq_div_two_le_normSpectralGap`,
  `SimpleGraph.conductance_sq_div_two_lt_normSpectralGap`,
  `SimpleGraph.conductance_sq_div_two_lt_normSpectralGap_of_connected`: Cheeger lower bound
  `h_G² / 2 ≤ λ_G` and strict inequality `h_G² / 2 < λ_G` ([Chung1997], Theorem 2.2).
* `SimpleGraph.algConnectivity_le_two_mul_isoperimetricNum`,
  `SimpleGraph.exists_card_sweep_cut_le`,
  `SimpleGraph.isoperimetricNum_sq_le_two_mul_maxDegree_mul_algConnectivity`,
  `SimpleGraph.isoperimetricNum_sq_div_two_mul_maxDegree_le_algConnectivity`: combinatorial
  Laplacian Cheeger inequality ([Chung1997], §2.5; [AlonMilman1985]).
* `SimpleGraph.IsRegularOfDegree.conductance_eq`,
  `SimpleGraph.IsRegularOfDegree.normSpectralGap_eq`: specialization to `d`-regular graphs.

## References

* [F. R. K. Chung, *Spectral Graph Theory*][Chung1997], Chapters 1–2.
* [N. Alon and V. D. Milman, *λ₁, Isoperimetric Inequalities for Graphs, and
  Superconcentrators*][AlonMilman1985].
-/

public section

open Finset Matrix

namespace SimpleGraph

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### Weighted medians and level-set co-area engine -/

section WeightedCoArea

omit G [DecidableRel G.Adj] in
/-- **Weighted finite median**: for any nonnegative vertex weights `w : V → ℝ` and score
`f : V → ℝ`, there exists a threshold `m : ℝ` such that both strict tails `{v | m < f v}` and
`{v | f v < m}` carry at most half the total weight `∑ v, w v`. -/
private theorem exists_weighted_median (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (f : V → ℝ) :
    ∃ m : ℝ,
      2 * (∑ v with m < f v, w v) ≤ ∑ v, w v ∧
      2 * (∑ v with f v < m, w v) ≤ ∑ v, w v := by
  classical
  rcases isEmpty_or_nonempty V with hV | hV
  · exact ⟨0, by simp, by simp⟩
  set W : ℝ := ∑ v : V, w v
  have hW : 0 ≤ W := sum_nonneg fun v _ => hw v
  set A : Finset V := univ.filter fun u => W ≤ 2 * ∑ v with f v ≤ f u, w v
  obtain ⟨v_max, -, hv_max⟩ := univ.exists_max_image f univ_nonempty
  have hA_ne : A.Nonempty := by
    refine ⟨v_max, mem_filter.2 ⟨mem_univ _, ?_⟩⟩
    have hall : (univ.filter fun v => f v ≤ f v_max) = univ :=
      filter_true_of_mem fun v _ => hv_max v (mem_univ v)
    rw [hall]
    linarith
  obtain ⟨v₀, hv₀A, hv₀_min⟩ := A.exists_min_image f hA_ne
  refine ⟨f v₀, ?_, ?_⟩
  · have hv₀W : W ≤ 2 * ∑ v with f v ≤ f v₀, w v := (mem_filter.1 hv₀A).2
    have hsplit : (∑ v with f v ≤ f v₀, w v) + (∑ v with f v₀ < f v, w v) = W := by
      simpa only [not_le] using sum_filter_add_sum_filter_not univ (fun v => f v ≤ f v₀) w
    linarith
  · set L : Finset V := univ.filter fun v => f v < f v₀
    rcases L.eq_empty_or_nonempty with hL | hL
    · rw [hL, sum_empty, mul_zero]
      exact hW
    · obtain ⟨v₁, hv₁L, hv₁_max⟩ := L.exists_max_image f hL
      have hv₁_lt : f v₁ < f v₀ := (mem_filter.1 hv₁L).2
      have hv₁_notA : v₁ ∉ A := fun hmem => not_le.2 hv₁_lt (hv₀_min v₁ hmem)
      simp only [A, mem_filter, mem_univ, true_and, not_le] at hv₁_notA
      have hL_eq : L = univ.filter fun v => f v ≤ f v₁ := by
        ext v
        simp only [L, mem_filter, mem_univ, true_and]
        exact ⟨fun hv => hv₁_max v (mem_filter.2 ⟨mem_univ v, hv⟩),
          fun hv => lt_of_le_of_lt hv hv₁_lt⟩
      rw [hL_eq]
      linarith

omit [Fintype V] G [DecidableRel G.Adj] in
private theorem sq_max_sub_max_add_sq_max_sub_max_le (a b : ℝ) :
    (max a 0 - max b 0) ^ 2 + (max (-a) 0 - max (-b) 0) ^ 2 ≤ (a - b) ^ 2 := by
  rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb | hb <;>
    simp only [max_eq_left, max_eq_right, ha, hb, neg_nonneg, neg_nonpos] <;> nlinarith

omit [Fintype V] G [DecidableRel G.Adj] in
private theorem sq_max_add_sq_max (a : ℝ) : max a 0 ^ 2 + max (-a) 0 ^ 2 = a ^ 2 := by
  rcases le_total a 0 with ha | ha <;>
    simp only [max_eq_left, max_eq_right, ha, neg_nonneg, neg_nonpos] <;> ring

omit [Fintype V] in
private theorem card_interedges_comm' (s t : Finset V) :
    #(G.interedges s t) = #(G.interedges t s) :=
  card_bij (fun e _ => e.swap) (fun _ he => G.swap_mem_interedges_iff.2 he)
    (fun _ _ _ _ h => Prod.swap_injective h)
    (fun e he => ⟨e.swap, G.swap_mem_interedges_iff.2 he, e.swap_swap⟩)

private theorem sum_interedges_univ_eq (h : V → V → ℝ) :
    (∑ e ∈ G.interedges univ univ, h e.1 e.2) =
      ∑ u : V, ∑ v : V, if G.Adj u v then h u v else 0 := by
  rw [SimpleGraph.interedges, Rel.interedges, sum_filter, sum_product]

private theorem sum_interedges_univ_fst (g : V → ℝ) :
    (∑ e ∈ G.interedges univ univ, g e.1) = ∑ u : V, g u * G.degree u := by
  rw [sum_interedges_univ_eq G (fun u _ => g u)]
  refine sum_congr rfl fun u _ => ?_
  rw [G.degree_eq_sum_if_adj (R := ℝ) u, mul_sum]
  refine sum_congr rfl fun v _ => ?_
  split_ifs <;> ring

private theorem sum_interedges_univ_snd (g : V → ℝ) :
    (∑ e ∈ G.interedges univ univ, g e.2) = ∑ v : V, g v * G.degree v := by
  have hswap : (∑ e ∈ G.interedges univ univ, g e.2) =
      ∑ e ∈ G.interedges univ univ, g e.1 := by
    refine sum_bij (fun e _ => e.swap) (fun _ he => G.swap_mem_interedges_iff.2 he)
      (fun _ _ _ _ h => Prod.swap_injective h)
      (fun e he => ⟨e.swap, G.swap_mem_interedges_iff.2 he, e.swap_swap⟩)
      (fun _ _ => rfl)
  rw [hswap, sum_interedges_univ_fst G]

variable [DecidableEq V]

/-- Each boundary edge of `A` is counted once in each orientation. -/
private theorem sum_boundary_indicator (A : Finset V) :
    ∑ e ∈ G.interedges univ univ, ((if e ∈ G.interedges A Aᶜ then (1 : ℝ) else 0) +
      if e ∈ G.interedges Aᶜ A then 1 else 0) = 2 * #(G.interedges A Aᶜ) := by
  rw [sum_add_distrib, sum_boole, sum_boole, filter_mem_eq_inter, filter_mem_eq_inter,
    inter_eq_right.2 (G.interedges_mono (subset_univ _) (subset_univ _)),
    inter_eq_right.2 (G.interedges_mono (subset_univ _) (subset_univ _)),
    ← card_interedges_comm' G A Aᶜ]
  ring

private theorem abs_sub_peel_min {T : Finset V} {ψ : V → ℝ}
    (hψ : ∀ v, 0 ≤ ψ v) (hT : ∀ v ∉ T, ψ v = 0) {v₀ : V} (hmin : ∀ v ∈ T, ψ v₀ ≤ ψ v)
    (e : V × V) (he : e ∈ G.interedges univ univ) :
    let ψ' : V → ℝ := fun v => if v ∈ T then ψ v - ψ v₀ else 0
    |ψ e.1 - ψ e.2| =
      |ψ' e.1 - ψ' e.2| + ψ v₀ * ((if e ∈ G.interedges T Tᶜ then 1 else 0) +
        if e ∈ G.interedges Tᶜ T then 1 else 0) := by
  intro ψ'
  have hadj : G.Adj e.1 e.2 := (G.mem_interedges_iff.1 he).2.2
  have habs : ∀ v ∈ T, |ψ v - ψ v₀| = ψ v - ψ v₀ := fun v hv =>
    abs_of_nonneg (sub_nonneg.2 (hmin v hv))
  by_cases h₁ : e.1 ∈ T <;> by_cases h₂ : e.2 ∈ T <;>
    simp only [ψ', G.mem_interedges_iff, mem_compl, h₁, h₂, hadj, hT, habs, ↓reduceIte,
      abs_of_nonneg (hψ _), not_true_eq_false, not_false_eq_true, and_true, and_false, sub_zero,
      zero_sub, abs_neg, sub_sub_sub_cancel_right] <;> ring

/-- **Weighted level-set co-area inequality**: if every positive upper level set
`{v | ψ u ≤ ψ v}` (`0 < ψ u`) satisfies `c * ∑_{v : ψ u ≤ ψ v} w v ≤ #(G.interedges S Sᶜ)`,
then `2 * c * ∑ v, ψ v * w v ≤ ∑_{e ∈ G.interedges univ univ} |ψ e.1 - ψ e.2|`. -/
private theorem two_mul_sum_le_sum_abs_sub_of_level {c : ℝ} (w : V → ℝ) (ψ : V → ℝ)
    (hψ : ∀ v, 0 ≤ ψ v)
    (hlevel : ∀ u, 0 < ψ u →
      c * (∑ v with ψ u ≤ ψ v, w v) ≤
        #(G.interedges (univ.filter fun v => ψ u ≤ ψ v) (univ.filter fun v => ψ u ≤ ψ v)ᶜ)) :
    2 * c * ∑ v, ψ v * w v ≤ ∑ e ∈ G.interedges univ univ, |ψ e.1 - ψ e.2| := by
  set T : Finset V := univ.filter fun v => 0 < ψ v
  have hT_zero : ∀ v ∉ T, ψ v = 0 := fun v hv => by
    simp only [T, mem_filter, mem_univ, true_and, not_lt] at hv
    exact le_antisymm hv (hψ v)
  rcases T.eq_empty_or_nonempty with hT | hT_ne
  · have hzero : ∀ v, ψ v = 0 := fun v => hT_zero v (hT ▸ notMem_empty v)
    simp only [hzero, zero_mul, sum_const_zero, mul_zero, sub_self, abs_zero, le_rfl]
  · obtain ⟨v₀, hv₀T, hmin⟩ := T.exists_min_image ψ hT_ne
    have hv₀_pos : 0 < ψ v₀ := (mem_filter.1 hv₀T).2
    have hT_eq : T = univ.filter fun v => ψ v₀ ≤ ψ v := by
      ext v
      simp only [T, mem_filter, mem_univ, true_and]
      exact ⟨fun hv => hmin v (mem_filter.2 ⟨mem_univ v, hv⟩), fun hv => lt_of_lt_of_le hv₀_pos hv⟩
    let ψ' : V → ℝ := fun v => if v ∈ T then ψ v - ψ v₀ else 0
    have hψ'_nonneg : ∀ v, 0 ≤ ψ' v := fun v => by
      by_cases hv : v ∈ T <;> simp only [ψ', hv, ↓reduceIte, sub_nonneg, hmin, le_rfl]
    have hsub : (univ.filter fun v => 0 < ψ' v) ⊂ T := by
      rw [ssubset_iff_subset_ne]
      refine ⟨fun v hv => ?_, fun heq => ?_⟩
      · have hv' : 0 < ψ' v := (mem_filter.1 hv).2
        by_contra hnot
        simp only [ψ', hnot, ↓reduceIte, lt_irrefl] at hv'
      · have hmem : v₀ ∈ univ.filter fun v => 0 < ψ' v := heq ▸ hv₀T
        simp only [mem_filter, mem_univ, true_and, ψ', hv₀T, ↓reduceIte, sub_self,
          lt_irrefl] at hmem
    have hlevel' : ∀ u, 0 < ψ' u →
        c * (∑ v with ψ' u ≤ ψ' v, w v) ≤
          #(G.interedges (univ.filter fun v => ψ' u ≤ ψ' v)
            (univ.filter fun v => ψ' u ≤ ψ' v)ᶜ) := by
      intro u hu'
      have huT : u ∈ T := hsub.1 (mem_filter.2 ⟨mem_univ u, hu'⟩)
      have hu_pos : 0 < ψ u := (mem_filter.1 huT).2
      have hset_eq : (univ.filter fun v => ψ' u ≤ ψ' v) = univ.filter fun v => ψ u ≤ ψ v := by
        ext v
        simp only [mem_filter, mem_univ, true_and, ψ', huT, ↓reduceIte]
        by_cases hvT : v ∈ T
        · simp only [hvT, ↓reduceIte, sub_le_sub_iff_right]
        · simp only [hvT, ↓reduceIte, hT_zero v hvT]
          exact iff_of_false (not_le.2 (by simpa only [ψ', huT, ↓reduceIte] using hu'))
            (not_le.2 hu_pos)
      rw [hset_eq]
      exact hlevel u hu_pos
    have ih := two_mul_sum_le_sum_abs_sub_of_level w ψ' hψ'_nonneg hlevel'
    have hsum_w : ∑ v, ψ' v * w v = ∑ v, ψ v * w v - ψ v₀ * ∑ v ∈ T, w v := by
      have hsplit : ∑ v, ψ v * w v = ∑ v ∈ T, ψ v * w v := by
        refine (sum_subset (subset_univ T) fun v _ hv => ?_).symm
        rw [hT_zero v hv, zero_mul]
      have hsplit' : ∑ v, ψ' v * w v = ∑ v ∈ T, (ψ v - ψ v₀) * w v := by
        rw [← sum_subset (subset_univ T)]
        · exact sum_congr rfl fun v hv => by simp only [ψ', hv, ↓reduceIte]
        · intro v _ hv
          simp only [ψ', hv, ↓reduceIte, zero_mul]
      rw [hsplit, hsplit', mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun v _ => by ring
    rw [sum_congr rfl fun e he => abs_sub_peel_min G hψ hT_zero hmin e he, sum_add_distrib,
      ← mul_sum, sum_boundary_indicator]
    have hcut_T : c * (∑ v ∈ T, w v) ≤ #(G.interedges T Tᶜ) := by
      simpa only [← hT_eq] using hlevel v₀ hv₀_pos
    have hmul_T := mul_le_mul_of_nonneg_left hcut_T hv₀_pos.le
    rw [hsum_w] at ih
    linarith
termination_by #{v | 0 < ψ v}
decreasing_by exact card_lt_card hsub

/-- **Cauchy–Schwarz + co-area quadratic inequality** on nonnegative `φ : V → ℝ`:
if every positive upper level set of `φ` has boundary at least `c` times its `w`-weight (`0 ≤ c`),
then `(2 * c * ∑ v, φ v ^ 2 * w v) ^ 2 ≤ D * (4 * ∑ v, φ v ^ 2 * d_v - D)`, where
`D = ∑_{e ∈ G.interedges univ univ} (φ e.1 - φ e.2) ^ 2`. -/
private theorem four_mul_sq_mul_sum_sq_le {c : ℝ} (hc₀ : 0 ≤ c) (w : V → ℝ) (hw : ∀ v, 0 ≤ w v)
    (φ : V → ℝ) (hφ : ∀ v, 0 ≤ φ v)
    (hlevel : ∀ u, 0 < φ u →
      c * (∑ v with φ u ≤ φ v, w v) ≤
        #(G.interedges (univ.filter fun v => φ u ≤ φ v) (univ.filter fun v => φ u ≤ φ v)ᶜ)) :
    (2 * c * ∑ v, φ v ^ 2 * w v) ^ 2 ≤
      (∑ e ∈ G.interedges univ univ, (φ e.1 - φ e.2) ^ 2) *
        (4 * (∑ v, φ v ^ 2 * G.degree v) -
          ∑ e ∈ G.interedges univ univ, (φ e.1 - φ e.2) ^ 2) := by
  have hlevel_sq : ∀ u, 0 < φ u ^ 2 →
      c * (∑ v with φ u ^ 2 ≤ φ v ^ 2, w v) ≤
        #(G.interedges (univ.filter fun v => φ u ^ 2 ≤ φ v ^ 2)
          (univ.filter fun v => φ u ^ 2 ≤ φ v ^ 2)ᶜ) := by
    intro u hu2
    have hu : 0 < φ u := by nlinarith [hφ u]
    have heq : (fun v => φ u ^ 2 ≤ φ v ^ 2) = (fun v => φ u ≤ φ v) :=
      funext fun v => propext (pow_le_pow_iff_left₀ (hφ u) (hφ v) two_ne_zero)
    simpa only [heq] using hlevel u hu
  have hco := two_mul_sum_le_sum_abs_sub_of_level G w (fun v => φ v ^ 2) (fun v => sq_nonneg _)
    hlevel_sq
  have hfact : ∀ e : V × V, |φ e.1 ^ 2 - φ e.2 ^ 2| = |φ e.1 - φ e.2| * (φ e.1 + φ e.2) :=
    fun e => by rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (hφ _) (hφ _)), mul_comm]
  have hcs : (∑ e ∈ G.interedges univ univ, |φ e.1 ^ 2 - φ e.2 ^ 2|) ^ 2 ≤
      (∑ e ∈ G.interedges univ univ, (φ e.1 - φ e.2) ^ 2) *
        (∑ e ∈ G.interedges univ univ, (φ e.1 + φ e.2) ^ 2) := by
    simp_rw [hfact]
    simpa only [sq_abs] using sum_mul_sq_le_sq_mul_sq (G.interedges univ univ)
      (fun e => |φ e.1 - φ e.2|) (fun e => φ e.1 + φ e.2)
  have hplus : (∑ e ∈ G.interedges univ univ, (φ e.1 + φ e.2) ^ 2) =
      4 * (∑ v, φ v ^ 2 * G.degree v) -
        ∑ e ∈ G.interedges univ univ, (φ e.1 - φ e.2) ^ 2 := by
    have h1 : (∑ e ∈ G.interedges univ univ, (φ e.1 + φ e.2) ^ 2) +
        (∑ e ∈ G.interedges univ univ, (φ e.1 - φ e.2) ^ 2) =
          2 * ((∑ e ∈ G.interedges univ univ, φ e.1 ^ 2) +
            ∑ e ∈ G.interedges univ univ, φ e.2 ^ 2) := by
      rw [← sum_add_distrib, ← sum_add_distrib, mul_sum]
      exact sum_congr rfl fun e _ => by ring
    rw [sum_interedges_univ_fst G (fun v => φ v ^ 2),
      sum_interedges_univ_snd G (fun v => φ v ^ 2)] at h1
    linarith
  rw [← hplus]
  have hco_nn : 0 ≤ 2 * c * ∑ v, φ v ^ 2 * w v :=
    mul_nonneg (mul_nonneg zero_le_two hc₀) (sum_nonneg fun v _ => mul_nonneg (sq_nonneg _) (hw v))
  exact (pow_le_pow_left₀ hco_nn hco 2).trans hcs

end WeightedCoArea

/-! ### Volume and conductance (`h_G`) -/

section Conductance

/-- **Volume** `vol(S)` of a vertex subset `S ⊆ V` ([Chung1997], §2.2, p. 24): sum of the degrees
of the vertices in `S`. -/
@[expose]
def vol (S : Finset V) : ℕ := ∑ v ∈ S, G.degree v

/-- **Total volume** `vol(G) = ∑_{v ∈ V} d_v` ([Chung1997], §1.2, p. 5). -/
@[expose]
def totalVol : ℕ := G.vol univ

@[simp]
theorem vol_empty : G.vol ∅ = 0 := sum_empty

@[simp]
theorem vol_singleton (v : V) : G.vol {v} = G.degree v := sum_singleton _ _

theorem vol_mono {S T : Finset V} (hST : S ⊆ T) : G.vol S ≤ G.vol T :=
  sum_le_sum_of_subset hST

theorem totalVol_eq_two_mul_card_edgeFinset : G.totalVol = 2 * #G.edgeFinset := by
  classical
  exact G.sum_degrees_eq_twice_card_edges

@[simp]
theorem totalVol_eq_zero_iff : G.totalVol = 0 ↔ G = ⊥ := by
  classical
  rw [G.totalVol_eq_two_mul_card_edgeFinset, Nat.mul_eq_zero, or_iff_right (by omega),
    card_eq_zero, edgeFinset_eq_empty]

theorem IsRegularOfDegree.vol_eq {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
    (hd : G.IsRegularOfDegree d) (S : Finset V) :
    G.vol S = d * #S := by
  simp only [vol, hd.degree_eq, sum_const, smul_eq_mul, Nat.mul_comm]

private theorem degree_eq_zero_of_eq_bot (hbot : G = ⊥) (v : V) : G.degree v = 0 :=
  Nat.eq_zero_of_not_pos ((G.degree_pos_iff_exists_adj v).not.2 fun ⟨_, hw⟩ => by
    rw [hbot] at hw; exact hw)

variable [DecidableEq V]

theorem vol_add_vol_compl (S : Finset V) : G.vol S + G.vol Sᶜ = G.totalVol :=
  sum_add_sum_compl S _

omit [DecidableEq V] in
/-- In any loopless simple graph, every vertex `u` satisfies `2 * d_u ≤ vol(G)`, since each of the
`d_u` neighbors of `u` lies outside `{u}` and has degree at least `1`. -/
theorem two_mul_degree_le_totalVol (u : V) : 2 * G.degree u ≤ G.totalVol := by
  classical
  have hsub : G.neighborFinset u ⊆ ({u} : Finset V)ᶜ := fun w hw => by
    rw [mem_compl, mem_singleton]
    exact (G.ne_of_adj ((G.mem_neighborFinset u w).1 hw)).symm
  have hdeg : G.degree u ≤ G.vol ({u} : Finset V)ᶜ := by
    calc G.degree u
        = ∑ _w ∈ G.neighborFinset u, 1 := by
          simp only [sum_const, card_neighborFinset_eq_degree, smul_eq_mul, mul_one]
      _ ≤ ∑ w ∈ G.neighborFinset u, G.degree w := by
          refine sum_le_sum fun w hw => ?_
          exact (G.degree_pos_iff_exists_adj w).2 ⟨u, ((G.mem_neighborFinset u w).1 hw).symm⟩
      _ ≤ G.vol ({u} : Finset V)ᶜ := G.vol_mono hsub
  have hcompl := G.vol_add_vol_compl {u}
  rw [vol_singleton] at hcompl
  omega

/-- Every edge in `G.interedges S Sᶜ` starts in `S`, so `#(G.interedges S Sᶜ) ≤ vol(S)`. -/
theorem card_interedges_compl_le_vol (S : Finset V) : #(G.interedges S Sᶜ) ≤ G.vol S := by
  have hsub : G.interedges S Sᶜ ⊆ S.biUnion fun u => (G.neighborFinset u).map
      ⟨fun v => (u, v), fun _ _ h => (Prod.mk.inj h).2⟩ := by
    intro ⟨u, v⟩ he
    obtain ⟨hu, _, hadj⟩ := G.mem_interedges_iff.1 he
    exact mem_biUnion.2 ⟨u, hu, mem_map.2 ⟨v, (G.mem_neighborFinset u v).2 hadj, rfl⟩⟩
  calc #(G.interedges S Sᶜ)
      ≤ #(S.biUnion fun u => (G.neighborFinset u).map
          ⟨fun v => (u, v), fun _ _ h => (Prod.mk.inj h).2⟩) := card_le_card hsub
    _ ≤ ∑ u ∈ S, #((G.neighborFinset u).map
          ⟨fun v => (u, v), fun _ _ h => (Prod.mk.inj h).2⟩) := card_biUnion_le
    _ = G.vol S := by simp only [card_map, card_neighborFinset_eq_degree, vol]

/-- **Set conductance** `h_G(S) = |E(S, Sᶜ)| / min(vol S, vol Sᶜ)` ([Chung1997], §2.2, Eq. (2.1),
p. 24). -/
noncomputable def setConductance (S : Finset V) : ℝ :=
  (#(G.interedges S Sᶜ) : ℝ) / (min (G.vol S) (G.vol Sᶜ) : ℕ)

theorem setConductance_def (S : Finset V) :
    G.setConductance S = (#(G.interedges S Sᶜ) : ℝ) / (min (G.vol S) (G.vol Sᶜ) : ℕ) := by
  rfl

@[simp]
theorem setConductance_compl (S : Finset V) : G.setConductance Sᶜ = G.setConductance S := by
  simp only [setConductance, compl_compl, card_interedges_comm' G Sᶜ S, min_comm]

theorem setConductance_eq_of_two_mul_vol_le {S : Finset V} (hS : 2 * G.vol S ≤ G.totalVol) :
    G.setConductance S = (#(G.interedges S Sᶜ) : ℝ) / G.vol S := by
  have hcompl := G.vol_add_vol_compl S
  rw [setConductance, min_eq_left (by omega)]

/-- **Cheeger constant (conductance)** `h_G` ([Chung1997], §2.2, Eq. (2.2), p. 24): infimum of
`|E(S, Sᶜ)| / vol(S)` over vertex subsets `S` with `0 < vol(S)` and `2 * vol(S) ≤ vol(G)` (`0` on
edgeless graphs `G = ⊥`). Equivalent to `inf_{0 < min(vol S, vol Sᶜ)} h_G(S)` via
`conductance_eq_iInf_setConductance`. -/
noncomputable def conductance : ℝ :=
  ⨅ S : {S : Finset V // 0 < G.vol S ∧ 2 * G.vol S ≤ G.totalVol},
    (#(G.interedges S.val S.valᶜ) : ℝ) / G.vol S.val

theorem conductance_def :
    G.conductance =
      ⨅ S : {S : Finset V // 0 < G.vol S ∧ 2 * G.vol S ≤ G.totalVol},
        (#(G.interedges S.val S.valᶜ) : ℝ) / G.vol S.val := by
  rfl

theorem conductance_nonneg : 0 ≤ G.conductance := by
  exact Real.iInf_nonneg fun _ => by positivity

theorem conductance_eq_zero_of_eq_bot (hbot : G = ⊥) : G.conductance = 0 := by
  have hempty : IsEmpty {S : Finset V // 0 < G.vol S ∧ 2 * G.vol S ≤ G.totalVol} :=
    ⟨fun ⟨S, hpos, _⟩ => by
      simp only [vol, degree_eq_zero_of_eq_bot G hbot, sum_const_zero, lt_irrefl] at hpos⟩
  exact Real.iInf_of_isEmpty _

@[simp]
theorem conductance_bot : (⊥ : SimpleGraph V).conductance = 0 :=
  (⊥ : SimpleGraph V).conductance_eq_zero_of_eq_bot rfl

theorem conductance_mul_vol_le {S : Finset V} (hS : 2 * G.vol S ≤ G.totalVol) :
    G.conductance * G.vol S ≤ #(G.interedges S Sᶜ) := by
  rcases Nat.eq_zero_or_pos (G.vol S) with h0 | hpos
  · rw [h0, Nat.cast_zero, mul_zero]
    exact Nat.cast_nonneg _
  · have hb : BddBelow (Set.range
        fun S : {S : Finset V // 0 < G.vol S ∧ 2 * G.vol S ≤ G.totalVol} =>
          (#(G.interedges S.val S.valᶜ) : ℝ) / G.vol S.val) :=
      ⟨0, Set.forall_mem_range.2 fun _ => by positivity⟩
    rw [← le_div_iff₀ (Nat.cast_pos.2 hpos)]
    exact ciInf_le hb ⟨S, hpos, hS⟩

theorem conductance_le_setConductance {S : Finset V} (hpos : 0 < min (G.vol S) (G.vol Sᶜ)) :
    G.conductance ≤ G.setConductance S := by
  have hcompl := G.vol_add_vol_compl S
  rcases le_total (G.vol S) (G.vol Sᶜ) with hle | hle
  · have h2 : 2 * G.vol S ≤ G.totalVol := by omega
    have hvol_pos : 0 < G.vol S := by omega
    rw [G.setConductance_eq_of_two_mul_vol_le h2, le_div_iff₀ (Nat.cast_pos.2 hvol_pos)]
    exact G.conductance_mul_vol_le h2
  · have h2 : 2 * G.vol Sᶜ ≤ G.totalVol := by omega
    have hvol_pos : 0 < G.vol Sᶜ := by omega
    rw [← G.setConductance_compl S, G.setConductance_eq_of_two_mul_vol_le h2,
      le_div_iff₀ (Nat.cast_pos.2 hvol_pos)]
    exact G.conductance_mul_vol_le h2

omit [DecidableEq V] in
private theorem nonempty_validCut_of_ne_bot (hG : G ≠ ⊥) :
    Nonempty {S : Finset V // 0 < G.vol S ∧ 2 * G.vol S ≤ G.totalVol} := by
  classical
  obtain ⟨e, he⟩ := edgeFinset_nonempty.2 hG
  induction e using Sym2.ind with | _ u w =>
  have hu_pos : 0 < G.degree u := (G.degree_pos_iff_exists_adj u).2 ⟨w, mem_edgeFinset.1 he⟩
  exact ⟨⟨{u}, by simpa only [vol_singleton] using hu_pos,
    by simpa only [vol_singleton] using G.two_mul_degree_le_totalVol u⟩⟩

/-- Equivalence with [Chung1997], Eq. (2.2): `h_G = ⨅_{0 < min(vol S, vol Sᶜ)} h_G(S)`. -/
theorem conductance_eq_iInf_setConductance :
    G.conductance =
      ⨅ S : {S : Finset V // 0 < min (G.vol S) (G.vol Sᶜ)}, G.setConductance S.val := by
  by_cases hbot : G = ⊥
  · rw [G.conductance_eq_zero_of_eq_bot hbot]
    have hempty : IsEmpty {S : Finset V // 0 < min (G.vol S) (G.vol Sᶜ)} :=
      ⟨fun ⟨S, hpos⟩ => by
        simp only [vol, degree_eq_zero_of_eq_bot G hbot, sum_const_zero, min_self,
          lt_irrefl] at hpos⟩
    exact (Real.iInf_of_isEmpty _).symm
  · obtain ⟨⟨S₀, hS₀_pos, hS₀_2⟩⟩ := nonempty_validCut_of_ne_bot G hbot
    have hne1 : Nonempty {S : Finset V // 0 < G.vol S ∧ 2 * G.vol S ≤ G.totalVol} :=
      ⟨⟨S₀, hS₀_pos, hS₀_2⟩⟩
    have hne2 : Nonempty {S : Finset V // 0 < min (G.vol S) (G.vol Sᶜ)} := by
      have hcompl := G.vol_add_vol_compl S₀
      exact ⟨⟨S₀, by omega⟩⟩
    have hb2 : BddBelow (Set.range fun S : {S : Finset V // 0 < min (G.vol S) (G.vol Sᶜ)} =>
        G.setConductance S.val) :=
      ⟨0, Set.forall_mem_range.2 fun _ => by unfold setConductance; positivity⟩
    refine le_antisymm (le_ciInf fun S => G.conductance_le_setConductance S.property) ?_
    refine le_ciInf fun ⟨S, hpos, h2⟩ => ?_
    have hcompl := G.vol_add_vol_compl S
    have hmin_pos : 0 < min (G.vol S) (G.vol Sᶜ) := by omega
    calc (⨅ T : {T : Finset V // 0 < min (G.vol T) (G.vol Tᶜ)}, G.setConductance T.val)
        ≤ G.setConductance S := ciInf_le hb2 ⟨S, hmin_pos⟩
      _ = (#(G.interedges S Sᶜ) : ℝ) / G.vol S := G.setConductance_eq_of_two_mul_vol_le h2

theorem le_conductance_iff (hG : G ≠ ⊥) {c : ℝ} :
    c ≤ G.conductance ↔
      ∀ S : Finset V, 0 < G.vol S → 2 * G.vol S ≤ G.totalVol →
        c * G.vol S ≤ #(G.interedges S Sᶜ) := by
  have := nonempty_validCut_of_ne_bot G hG
  exact ⟨fun h S _ h2 =>
    (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _)).trans (G.conductance_mul_vol_le h2),
    fun h => le_ciInf fun ⟨S, hpos, h2⟩ => (le_div_iff₀ (Nat.cast_pos.2 hpos)).2 (h S hpos h2)⟩

/-- For every finite simple graph, `h_G ≤ 1` (witnessed by a singleton positive-degree vertex when
`G ≠ ⊥`). -/
theorem conductance_le_one : G.conductance ≤ 1 := by
  by_cases hbot : G = ⊥
  · rw [G.conductance_eq_zero_of_eq_bot hbot]
    exact zero_le_one
  · obtain ⟨⟨S, hS_pos, hS_2⟩⟩ := nonempty_validCut_of_ne_bot G hbot
    have hmul := G.conductance_mul_vol_le hS_2
    have hreal : (#(G.interedges S Sᶜ) : ℝ) ≤ G.vol S := by
      exact_mod_cast G.card_interedges_compl_le_vol S
    have hvol_pos : (0 : ℝ) < G.vol S := Nat.cast_pos.2 hS_pos
    exact (le_div_iff₀ hvol_pos).2 (hmul.trans hreal) |>.trans_eq (div_self hvol_pos.ne')

/-- For any connected simple graph on at least two vertices, `2 / vol(G) ≤ h_G`
([Chung1997], §2.3, p. 28). -/
theorem two_div_totalVol_le_conductance [Nontrivial V] (hconn : G.Connected) :
    2 / (G.totalVol : ℝ) ≤ G.conductance := by
  have hne_bot : G ≠ ⊥ := by
    obtain ⟨u, w, huw⟩ := exists_pair_ne V
    obtain ⟨p⟩ := hconn u w
    rcases p with _ | @⟨_, x, _, hadj, _⟩
    · exact absurd rfl huw
    · intro hbot
      rw [hbot] at hadj
      exact hadj
  have htot_pos : (0 : ℝ) < G.totalVol :=
    Nat.cast_pos.2 (Nat.pos_of_ne_zero (G.totalVol_eq_zero_iff.not.2 hne_bot))
  refine (G.le_conductance_iff hne_bot).2 fun S hpos h2 => ?_
  obtain ⟨u, huS⟩ := S.nonempty_of_ne_empty
    (by intro h; simp only [h, vol_empty, lt_irrefl] at hpos)
  have hcompl_pos : 0 < G.vol Sᶜ := by
    have h := G.vol_add_vol_compl S
    omega
  obtain ⟨w, hwS⟩ := Sᶜ.nonempty_of_ne_empty
    (by intro h; simp only [h, vol_empty, lt_irrefl] at hcompl_pos)
  obtain ⟨p⟩ := hconn u w
  obtain ⟨d, -, hdS, hdS'⟩ := p.exists_boundary_dart (S : Set V) huS (mem_compl.1 hwS)
  have hmem : (d.fst, d.snd) ∈ G.interedges S Sᶜ :=
    G.mk_mem_interedges_iff.2 ⟨hdS, mem_compl.2 hdS', d.adj⟩
  have hcard1 : (1 : ℝ) ≤ #(G.interedges S Sᶜ) :=
    Nat.one_le_cast.2 (Finset.card_pos.2 ⟨_, hmem⟩)
  have h2' : 2 * (G.vol S : ℝ) ≤ G.totalVol := by exact_mod_cast h2
  rw [div_mul_eq_mul_div, div_le_iff₀ htot_pos]
  nlinarith

/-- On at least two vertices with no isolated vertices, `G` is connected iff `0 < h_G`
([Chung1997], §2.2, p. 24). -/
theorem connected_iff_conductance_pos [Nontrivial V] (hiso : ∀ v, 0 < G.degree v) :
    G.Connected ↔ 0 < G.conductance := by
  refine ⟨fun hconn => ?_, fun hpos => ?_⟩
  · obtain ⟨u, _, _⟩ := exists_pair_ne V
    have htot_pos : (0 : ℝ) < G.totalVol :=
      Nat.cast_pos.2 (lt_of_lt_of_le (hiso u) (G.vol_mono (subset_univ {u}) |>.trans_eq rfl))
    exact lt_of_lt_of_le (div_pos zero_lt_two htot_pos) (G.two_div_totalVol_le_conductance hconn)
  · obtain ⟨u₀⟩ := (inferInstance : Nonempty V)
    refine (G.connected_iff_exists_forall_reachable).2 ⟨u₀, fun w => ?_⟩
    by_contra hnr
    set S : Finset V := univ.filter fun x => G.Reachable u₀ x
    have hu₀S : u₀ ∈ S := mem_filter.2 ⟨mem_univ u₀, Reachable.refl u₀⟩
    have hwS : w ∈ Sᶜ := mem_compl.2 (by simp only [S, mem_filter, mem_univ, true_and]; exact hnr)
    have hvolS : 0 < G.vol S := lt_of_lt_of_le (hiso u₀) (G.vol_mono (singleton_subset_iff.2 hu₀S))
    have hvolSc : 0 < G.vol Sᶜ := lt_of_lt_of_le (hiso w) (G.vol_mono (singleton_subset_iff.2 hwS))
    have hempty_inter : G.interedges S Sᶜ = ∅ := by
      ext ⟨x, y⟩
      simp only [G.mem_interedges_iff, mem_compl, S, mem_filter, mem_univ, true_and,
        notMem_empty, iff_false, not_and]
      intro hx hny hxy
      exact hny (hx.trans ⟨Walk.cons hxy Walk.nil⟩)
    have hsc : G.setConductance S = 0 := by
      simp only [setConductance, hempty_inter, card_empty, Nat.cast_zero, zero_div]
    have hle := G.conductance_le_setConductance (S := S) (by omega)
    linarith

end Conductance

/-! ### Normalized Laplacian `𝓛_G` and normalized spectral gap `λ_G` -/

section NormalizedLaplacian

variable [DecidableEq V]

/-- Inverse-square-root degree matrix `T^{-1/2}` ([Chung1997], §1.2, p. 2), with convention
`T^{-1/2}(v, v) = 0` at isolated vertices `d_v = 0` (since `Real.sqrt 0 = 0` and `0⁻¹ = 0`). -/
noncomputable def degInvSqrtMatrix : Matrix V V ℝ :=
  diagonal fun v => (Real.sqrt (G.degree v))⁻¹

theorem degInvSqrtMatrix_def :
    G.degInvSqrtMatrix = diagonal fun v => (Real.sqrt (G.degree v))⁻¹ := by
  rfl

/-- **Normalized Laplacian matrix** `𝓛_G = T^{-1/2} L T^{-1/2}` ([Chung1997], §1.2, p. 2). -/
noncomputable def normLapMatrix : Matrix V V ℝ :=
  G.degInvSqrtMatrix * G.lapMatrix ℝ * G.degInvSqrtMatrix

theorem normLapMatrix_def :
    G.normLapMatrix = G.degInvSqrtMatrix * G.lapMatrix ℝ * G.degInvSqrtMatrix := by
  rfl

/-- Entrywise formula for `𝓛_G` ([Chung1997], §1.2, p. 2):
`1` on the diagonal when `d_v ≠ 0`, `-1 / √(d_u d_v)` when `G.Adj u v`, and `0` otherwise. -/
theorem normLapMatrix_apply (u v : V) :
    G.normLapMatrix u v =
      if u = v then (if G.degree v = 0 then 0 else 1)
      else if G.Adj u v then -(Real.sqrt (G.degree u * G.degree v))⁻¹
      else 0 := by
  simp only [normLapMatrix, degInvSqrtMatrix, diagonal_mul, mul_diagonal, lapMatrix,
    degMatrix, Matrix.sub_apply, diagonal_apply, adjMatrix_apply]
  rcases eq_or_ne u v with rfl | huv
  · simp only [↓reduceIte, G.loopless.irrefl u, sub_zero]
    rcases Nat.eq_zero_or_pos (G.degree u) with h0 | hpos
    · simp only [h0, ↓reduceIte, Nat.cast_zero, Real.sqrt_zero, _root_.inv_zero, zero_mul]
    · have hne : G.degree u ≠ 0 := hpos.ne'
      have hcast_pos : (0 : ℝ) < G.degree u := Nat.cast_pos.2 hpos
      have hsqrt_ne : Real.sqrt (G.degree u) ≠ 0 := (Real.sqrt_pos.2 hcast_pos).ne'
      simp only [hne, ↓reduceIte]
      field_simp [hsqrt_ne]
      exact (Real.sq_sqrt hcast_pos.le).symm
  · simp only [huv, ↓reduceIte]
    by_cases hadj : G.Adj u v
    · simp only [hadj, ↓reduceIte, Real.sqrt_mul (Nat.cast_nonneg _), _root_.mul_inv_rev]
      ring
    · simp only [hadj, ↓reduceIte, sub_zero, mul_zero, zero_mul]

theorem isSymm_degInvSqrtMatrix : G.degInvSqrtMatrix.IsSymm := by
  exact isSymm_diagonal _

theorem isSymm_normLapMatrix : G.normLapMatrix.IsSymm := by
  rw [IsSymm, normLapMatrix, transpose_mul, transpose_mul, G.isSymm_degInvSqrtMatrix.eq,
    (G.isSymm_lapMatrix ℝ).eq, Matrix.mul_assoc]

theorem isHermitian_normLapMatrix : G.normLapMatrix.IsHermitian := by
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
  exact G.isSymm_normLapMatrix

/-- `𝓛_G` is positive semidefinite ([Chung1997], §1.2, p. 3). -/
theorem posSemidef_normLapMatrix : G.normLapMatrix.PosSemidef := by
  have hconj : G.degInvSqrtMatrixᴴ = G.degInvSqrtMatrix := by
    rw [conjTranspose_eq_transpose_of_trivial]
    exact G.isSymm_degInvSqrtMatrix
  rw [normLapMatrix]
  nth_rw 1 [← hconj]
  exact (G.posSemidef_lapMatrix ℝ).conjTranspose_mul_mul_same G.degInvSqrtMatrix

/-- For a `d`-regular graph with `0 < d`, `𝓛_G = I - (1 / d) A` ([Chung1997], §1.2, p. 3). -/
theorem IsRegularOfDegree.normLapMatrix_eq {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
    (hd : G.IsRegularOfDegree d) (hd_pos : 0 < d) :
    G.normLapMatrix = 1 - (d : ℝ)⁻¹ • G.adjMatrix ℝ := by
  ext u v
  rw [G.normLapMatrix_apply]
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, adjMatrix_apply, smul_eq_mul]
  rcases eq_or_ne u v with rfl | huv
  · simp only [↓reduceIte, hd.degree_eq u, hd_pos.ne', G.loopless.irrefl u, mul_zero, sub_zero]
  · simp only [huv, ↓reduceIte, hd.degree_eq u, hd.degree_eq v]
    by_cases hadj : G.Adj u v
    · have hd_nn : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      simp only [hadj, ↓reduceIte, ← sq, Real.sqrt_sq hd_nn, mul_one, zero_sub]
    · simp only [hadj, ↓reduceIte, mul_zero, sub_zero]

/-- `T^{1/2} 1 = (v ↦ √(d_v))` lies in the kernel of `𝓛_G` ([Chung1997], §1.2, p. 4). -/
theorem normLapMatrix_mulVec_sqrt_degree :
    G.normLapMatrix *ᵥ (fun v => Real.sqrt (G.degree v)) = 0 := by
  have hproj : G.degInvSqrtMatrix *ᵥ (fun v => Real.sqrt (G.degree v)) =
      fun v => if G.degree v = 0 then 0 else 1 := by
    ext v
    simp only [degInvSqrtMatrix, mulVec_diagonal]
    rcases Nat.eq_zero_or_pos (G.degree v) with h0 | hpos
    · simp only [h0, ↓reduceIte, Nat.cast_zero, Real.sqrt_zero, _root_.inv_zero, mul_zero]
    · simp only [hpos.ne', ↓reduceIte,
        inv_mul_cancel₀ (Real.sqrt_pos.2 (Nat.cast_pos.2 hpos)).ne']
  have hlap : G.lapMatrix ℝ *ᵥ (fun v => if G.degree v = 0 then (0 : ℝ) else 1) = 0 := by
    rw [lapMatrix_mulVec_eq_zero_iff_forall_adj]
    intro u v hadj
    have hu : G.degree u ≠ 0 := ((G.degree_pos_iff_exists_adj u).2 ⟨v, hadj⟩).ne'
    have hv : G.degree v ≠ 0 := ((G.degree_pos_iff_exists_adj v).2 ⟨u, hadj.symm⟩).ne'
    simp only [hu, hv, ↓reduceIte]
  rw [normLapMatrix, Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec, hproj, hlap, mulVec_zero]

/-- Combinatorial Dirichlet identity:
`f ⬝ᵥ (L *ᵥ f) = (1 / 2) ∑_{e ∈ interedges univ univ} (f e.1 - f e.2)²`. -/
theorem dotProduct_mulVec_lapMatrix (f : V → ℝ) :
    f ⬝ᵥ (G.lapMatrix ℝ *ᵥ f) =
      (∑ e ∈ G.interedges univ univ, (f e.1 - f e.2) ^ 2) / 2 := by
  rw [← toLinearMap₂'_apply', G.lapMatrix_toLinearMap₂' ℝ f,
    ← sum_interedges_univ_eq G (fun u v => (f u - f v) ^ 2)]

/-- Change-of-variables identity ([Chung1997], Eq. (1.1), p. 3): when `g v = √(d_v) * f v`,
`g ⬝ᵥ (𝓛_G *ᵥ g) = f ⬝ᵥ (L *ᵥ f)`. -/
theorem dotProduct_mulVec_normLapMatrix_mul_sqrt (f : V → ℝ) :
    (fun v => Real.sqrt (G.degree v) * f v) ⬝ᵥ
        (G.normLapMatrix *ᵥ fun v => Real.sqrt (G.degree v) * f v) =
      f ⬝ᵥ (G.lapMatrix ℝ *ᵥ f) := by
  set g : V → ℝ := fun v => Real.sqrt (G.degree v) * f v
  set f₀ : V → ℝ := G.degInvSqrtMatrix *ᵥ g
  have hf₀_apply : ∀ v, f₀ v = if G.degree v = 0 then 0 else f v := fun v => by
    simp only [f₀, g, degInvSqrtMatrix, mulVec_diagonal]
    rcases Nat.eq_zero_or_pos (G.degree v) with h0 | hpos
    · simp only [h0, ↓reduceIte, Nat.cast_zero, Real.sqrt_zero, _root_.inv_zero, zero_mul]
    · simp only [hpos.ne', ↓reduceIte,
        inv_mul_cancel_left₀ (Real.sqrt_pos.2 (Nat.cast_pos.2 hpos)).ne']
  have hvec : g ᵥ* G.degInvSqrtMatrix = f₀ := by
    ext v
    simp only [f₀, degInvSqrtMatrix, vecMul_diagonal, mulVec_diagonal, mul_comm]
  have hlhs : g ⬝ᵥ (G.normLapMatrix *ᵥ g) = f₀ ⬝ᵥ (G.lapMatrix ℝ *ᵥ f₀) := by
    rw [normLapMatrix, Matrix.mul_assoc, ← mulVec_mulVec, dotProduct_mulVec, hvec, ← mulVec_mulVec]
  rw [hlhs, G.dotProduct_mulVec_lapMatrix, G.dotProduct_mulVec_lapMatrix]
  congr 1
  refine sum_congr rfl fun e he => ?_
  have hadj := (G.mem_interedges_iff.1 he).2.2
  have he1 : G.degree e.1 ≠ 0 := ((G.degree_pos_iff_exists_adj e.1).2 ⟨e.2, hadj⟩).ne'
  have he2 : G.degree e.2 ≠ 0 := ((G.degree_pos_iff_exists_adj e.2).2 ⟨e.1, hadj.symm⟩).ne'
  simp only [hf₀_apply, he1, he2, ↓reduceIte]

/-- **Normalized Rayleigh quotient** `R_G(f) = (f ⬝ᵥ L f) / ∑_v f(v)² d_v`
([Chung1997], Eq. (1.1), p. 3). -/
noncomputable def normRayleigh (f : V → ℝ) : ℝ :=
  (f ⬝ᵥ (G.lapMatrix ℝ *ᵥ f)) / (∑ v, f v ^ 2 * G.degree v)

theorem normRayleigh_def (f : V → ℝ) :
    G.normRayleigh f = (f ⬝ᵥ (G.lapMatrix ℝ *ᵥ f)) / (∑ v, f v ^ 2 * G.degree v) := by
  rfl

theorem normRayleigh_nonneg (f : V → ℝ) : 0 ≤ G.normRayleigh f := by
  rw [normRayleigh, G.dotProduct_mulVec_lapMatrix]
  exact div_nonneg (div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) zero_le_two)
    (sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _))

theorem normRayleigh_le_two (f : V → ℝ) : G.normRayleigh f ≤ 2 := by
  rw [normRayleigh, G.dotProduct_mulVec_lapMatrix]
  set N : ℝ := ∑ v, f v ^ 2 * G.degree v
  have hN_nn : 0 ≤ N := sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  rcases hN_nn.eq_or_lt with hN | hN
  · rw [← hN, div_zero]
    exact zero_le_two
  · rw [div_le_iff₀ hN, div_le_iff₀ zero_lt_two]
    have hle : (∑ e ∈ G.interedges univ univ, (f e.1 - f e.2) ^ 2) ≤
        2 * ((∑ e ∈ G.interedges univ univ, f e.1 ^ 2) +
          ∑ e ∈ G.interedges univ univ, f e.2 ^ 2) := by
      rw [← sum_add_distrib, mul_sum]
      exact sum_le_sum fun e _ => by nlinarith [sq_nonneg (f e.1 + f e.2)]
    rw [sum_interedges_univ_fst G (fun v => f v ^ 2),
      sum_interedges_univ_snd G (fun v => f v ^ 2)] at hle
    simp only [N] at hN ⊢
    linarith

/-- **Normalized spectral gap** `λ_G` ([Chung1997], Eq. (1.2), p. 4): infimum of
`G.normRayleigh f` over `f : V → ℝ` orthogonal to degrees (`∑ v, f v * d_v = 0`) with
`0 < ∑ v, f v ^ 2 * d_v` (`0` on edgeless graphs `G = ⊥`). When `G` has no isolated vertices,
`normSpectralGap` equals the second eigenvalue `λ_1` of `G.normLapMatrix`; isolated vertices
contribute additional `0` eigenvalues to `G.normLapMatrix` while `G.normRayleigh` ignores
`d_v = 0` coordinates. -/
noncomputable def normSpectralGap : ℝ :=
  ⨅ f : {f : V → ℝ // ∑ v, f v * G.degree v = 0 ∧ 0 < ∑ v, f v ^ 2 * G.degree v},
    G.normRayleigh f.val

theorem normSpectralGap_def :
    G.normSpectralGap =
      ⨅ f : {f : V → ℝ // ∑ v, f v * G.degree v = 0 ∧ 0 < ∑ v, f v ^ 2 * G.degree v},
        G.normRayleigh f.val := by
  rfl

theorem normSpectralGap_nonneg : 0 ≤ G.normSpectralGap := by
  exact Real.iInf_nonneg fun f => G.normRayleigh_nonneg f.val

theorem normSpectralGap_eq_zero_of_eq_bot (hbot : G = ⊥) : G.normSpectralGap = 0 := by
  have hempty : IsEmpty
      {f : V → ℝ // ∑ v, f v * G.degree v = 0 ∧ 0 < ∑ v, f v ^ 2 * G.degree v} :=
    ⟨fun ⟨_, _, hpos⟩ => by
      simp only [degree_eq_zero_of_eq_bot G hbot, Nat.cast_zero, mul_zero, sum_const_zero,
        lt_irrefl] at hpos⟩
  exact Real.iInf_of_isEmpty _

@[simp]
theorem normSpectralGap_bot : (⊥ : SimpleGraph V).normSpectralGap = 0 :=
  (⊥ : SimpleGraph V).normSpectralGap_eq_zero_of_eq_bot rfl

private theorem pair_orthog_sum {a b : V} (hab : a ≠ b) :
    ∑ v, (if v = a then (G.degree b : ℝ) else if v = b then -(G.degree a : ℝ) else 0) *
      G.degree v = 0 := by
  let f : V → ℝ := fun v =>
    if v = a then G.degree b else if v = b then -(G.degree a : ℝ) else 0
  have hsub : ∑ v, f v * G.degree v = ∑ v ∈ ({a, b} : Finset V), f v * G.degree v := by
    refine (sum_subset (subset_univ _) fun v _ hv => ?_).symm
    rw [mem_insert, mem_singleton, not_or] at hv
    simp only [f, hv.1, hv.2, ↓reduceIte, zero_mul]
  change ∑ v, f v * G.degree v = 0
  rw [hsub, sum_pair hab]
  simp only [f, hab.symm, ↓reduceIte]
  ring

omit [DecidableEq V] in
private theorem nonempty_orthog_of_ne_bot (hG : G ≠ ⊥) :
    Nonempty {f : V → ℝ // ∑ v, f v * G.degree v = 0 ∧ 0 < ∑ v, f v ^ 2 * G.degree v} := by
  classical
  obtain ⟨e, he⟩ := edgeFinset_nonempty.2 hG
  induction e using Sym2.ind with | _ u w =>
  have hadj : G.Adj u w := mem_edgeFinset.1 he
  have huw : u ≠ w := G.ne_of_adj hadj
  have hdu : (0 : ℝ) < G.degree u := Nat.cast_pos.2 ((G.degree_pos_iff_exists_adj u).2 ⟨w, hadj⟩)
  have hdw : (0 : ℝ) < G.degree w :=
    Nat.cast_pos.2 ((G.degree_pos_iff_exists_adj w).2 ⟨u, hadj.symm⟩)
  let f : V → ℝ := fun v => if v = u then G.degree w else if v = w then -(G.degree u : ℝ) else 0
  have hpos : 0 < ∑ v, f v ^ 2 * G.degree v := by
    have hterm : 0 < f u ^ 2 * G.degree u := by simp only [f, ↓reduceIte]; positivity
    exact lt_of_lt_of_le hterm (single_le_sum (f := fun v => f v ^ 2 * (G.degree v : ℝ))
      (fun v _ => mul_nonneg (sq_nonneg (f v)) (Nat.cast_nonneg _)) (mem_univ u))
  exact ⟨⟨f, pair_orthog_sum G huw, hpos⟩⟩

theorem normSpectralGap_le_normRayleigh {f : V → ℝ}
    (horth : ∑ v, f v * G.degree v = 0) (hpos : 0 < ∑ v, f v ^ 2 * G.degree v) :
    G.normSpectralGap ≤ G.normRayleigh f := by
  have hb : BddBelow (Set.range fun g : {f : V → ℝ //
      ∑ v, f v * G.degree v = 0 ∧ 0 < ∑ v, f v ^ 2 * G.degree v} => G.normRayleigh g.val) :=
    ⟨0, Set.forall_mem_range.2 fun g => G.normRayleigh_nonneg g.val⟩
  exact ciInf_le hb ⟨f, horth, hpos⟩

theorem le_normSpectralGap_iff (hG : G ≠ ⊥) {c : ℝ} :
    c ≤ G.normSpectralGap ↔
      ∀ f : V → ℝ, ∑ v, f v * G.degree v = 0 → 0 < ∑ v, f v ^ 2 * G.degree v →
        c ≤ G.normRayleigh f := by
  have := nonempty_orthog_of_ne_bot G hG
  exact ⟨fun hc f hf hpos => hc.trans (G.normSpectralGap_le_normRayleigh hf hpos),
    fun h => le_ciInf fun ⟨f, hf, hpos⟩ => h f hf hpos⟩

/-- `λ_G ≤ 2` for every finite simple graph ([Chung1997], Lemma 1.7(v), p. 7). -/
theorem normSpectralGap_le_two : G.normSpectralGap ≤ 2 := by
  by_cases hbot : G = ⊥
  · rw [G.normSpectralGap_eq_zero_of_eq_bot hbot]
    exact zero_le_two
  · obtain ⟨⟨f, hf, hpos⟩⟩ := nonempty_orthog_of_ne_bot G hbot
    exact (G.normSpectralGap_le_normRayleigh hf hpos).trans (G.normRayleigh_le_two f)

/-- For the complete graph `K_n` (`⊤ : SimpleGraph V`) on `n ≥ 2` vertices,
`λ_{K_n} = n / (n - 1)` ([Chung1997], Example 1.1 & Lemma 1.7(ii), p. 6). -/
theorem normSpectralGap_top (hn : 2 ≤ Fintype.card V) :
    (⊤ : SimpleGraph V).normSpectralGap = (Fintype.card V : ℝ) / (Fintype.card V - 1) := by
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  have htop_ne : (⊤ : SimpleGraph V) ≠ ⊥ := top_ne_bot
  have hd_pos : (0 : ℝ) < (Fintype.card V : ℝ) - 1 := by
    have : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
    linarith
  have hd_nat : ∀ v : V, ((⊤ : SimpleGraph V).degree v : ℝ) = (Fintype.card V : ℝ) - 1 := by
    intro v
    have hd_eq : (⊤ : SimpleGraph V).degree v = Fintype.card V - 1 := by simp
    rw [hd_eq, Nat.cast_sub (by omega), Nat.cast_one]
  have hray : ∀ f : V → ℝ,
      ∑ v, f v * ((⊤ : SimpleGraph V).degree v : ℝ) = 0 →
      0 < ∑ v, f v ^ 2 * ((⊤ : SimpleGraph V).degree v : ℝ) →
      (⊤ : SimpleGraph V).normRayleigh f = (Fintype.card V : ℝ) / (Fintype.card V - 1) := by
    intro f horth hpos
    simp_rw [hd_nat, ← sum_mul] at horth hpos
    have hsum_f : ∑ v, f v = 0 := (mul_eq_zero.1 horth).resolve_right hd_pos.ne'
    have hsq_pos : 0 < ∑ v, f v ^ 2 := pos_of_mul_pos_left hpos hd_pos.le
    have hlap : f ⬝ᵥ ((⊤ : SimpleGraph V).lapMatrix ℝ *ᵥ f) =
        (Fintype.card V : ℝ) * ∑ v, f v ^ 2 := by
      have hall : ∀ u v : V,
          (if (⊤ : SimpleGraph V).Adj u v then (f u - f v) ^ 2 else 0) = (f u - f v) ^ 2 := by
        intro u v
        rcases eq_or_ne u v with rfl | huv <;> simp [*]
      rw [(⊤ : SimpleGraph V).dotProduct_mulVec_lapMatrix,
        sum_interedges_univ_eq (⊤ : SimpleGraph V) (fun u v => (f u - f v) ^ 2)]
      simp only [hall]
      simp only [sub_sq, sum_add_distrib, sum_sub_distrib, ← mul_sum, hsum_f, mul_zero,
        sum_const, card_univ, nsmul_eq_mul, sub_zero]
      ring
    rw [normRayleigh, hlap]
    simp_rw [hd_nat, ← sum_mul]
    rw [mul_comm (Fintype.card V : ℝ), mul_div_mul_left _ _ hsq_pos.ne']
  obtain ⟨⟨f₀, hf₀, hpos₀⟩⟩ := nonempty_orthog_of_ne_bot (⊤ : SimpleGraph V) htop_ne
  refine le_antisymm ?_ ((le_normSpectralGap_iff _ htop_ne).2 fun f hf hp => (hray f hf hp).ge)
  exact ((⊤ : SimpleGraph V).normSpectralGap_le_normRayleigh hf₀ hpos₀).trans_eq (hray f₀ hf₀ hpos₀)

/-- If `G` contains two distinct nonadjacent positive-degree vertices, then `λ_G ≤ 1`
([Chung1997], Lemma 1.7(iii), p. 7). -/
theorem normSpectralGap_le_one_of_ne_top {a b : V} (hab : a ≠ b) (hnadj : ¬ G.Adj a b)
    (hda : 0 < G.degree a) (hdb : 0 < G.degree b) :
    G.normSpectralGap ≤ 1 := by
  let f : V → ℝ := fun v =>
    if v = a then G.degree b else if v = b then -(G.degree a : ℝ) else 0
  have horth : ∑ v, f v * G.degree v = 0 := pair_orthog_sum G hab
  have hdenom : ∑ v, f v ^ 2 * G.degree v =
      (G.degree b : ℝ) ^ 2 * G.degree a + (G.degree a : ℝ) ^ 2 * G.degree b := by
    have hsub : ∑ v, f v ^ 2 * G.degree v = ∑ v ∈ ({a, b} : Finset V), f v ^ 2 * G.degree v := by
      refine (sum_subset (subset_univ _) fun v _ hv => ?_).symm
      rw [mem_insert, mem_singleton, not_or] at hv
      simp only [f, hv.1, hv.2, ↓reduceIte, zero_pow two_ne_zero, zero_mul]
    rw [hsub, sum_pair hab]
    simp only [f, hab.symm, ↓reduceIte]
    ring
  have hda' : (0 : ℝ) < G.degree a := Nat.cast_pos.2 hda
  have hdb' : (0 : ℝ) < G.degree b := Nat.cast_pos.2 hdb
  have hpos : 0 < ∑ v, f v ^ 2 * G.degree v := by rw [hdenom]; positivity
  refine (G.normSpectralGap_le_normRayleigh horth hpos).trans ?_
  rw [normRayleigh, div_le_one hpos, G.dotProduct_mulVec_lapMatrix]
  have hcross : ∀ e ∈ G.interedges univ univ, f e.1 * f e.2 = 0 := by
    intro ⟨x, y⟩ he
    have hadj : G.Adj x y := (G.mem_interedges_iff.1 he).2.2
    have hyx : y ≠ x := (G.ne_of_adj hadj).symm
    rcases eq_or_ne x a with rfl | hxa
    · simp only [f, hyx, show y ≠ b from fun hy => hnadj (hy ▸ hadj), ↓reduceIte, mul_zero]
    rcases eq_or_ne x b with rfl | hxb
    · simp only [f, hxa, hyx, show y ≠ a from fun hy => hnadj (hy ▸ hadj.symm), ↓reduceIte,
        mul_zero]
    · simp only [f, hxa, hxb, ↓reduceIte, zero_mul]
  have hsq : ∀ e ∈ G.interedges univ univ, (f e.1 - f e.2) ^ 2 = f e.1 ^ 2 + f e.2 ^ 2 :=
    fun e he => by nlinarith [hcross e he]
  rw [sum_congr rfl hsq, sum_add_distrib, sum_interedges_univ_fst G (fun v => f v ^ 2),
    sum_interedges_univ_snd G (fun v => f v ^ 2)]
  linarith

end NormalizedLaplacian

/-! ### Normalized Cheeger inequality and sweep-cut rounding -/

section NormalizedCheeger

variable [DecidableEq V]

private theorem dotProduct_mulVec_lapMatrix_twoVal (A : Finset V) (a b : ℝ) :
    (fun v => if v ∈ A then a else b) ⬝ᵥ
        (G.lapMatrix ℝ *ᵥ fun v => if v ∈ A then a else b) =
      #(G.interedges A Aᶜ) * (a - b) ^ 2 := by
  let f : V → ℝ := fun v => if v ∈ A then a else b
  change f ⬝ᵥ (G.lapMatrix ℝ *ᵥ f) = _
  rw [G.dotProduct_mulVec_lapMatrix]
  have hterm : ∀ e ∈ G.interedges univ univ, (f e.1 - f e.2) ^ 2 =
      (a - b) ^ 2 * ((if e ∈ G.interedges A Aᶜ then 1 else 0) +
        if e ∈ G.interedges Aᶜ A then 1 else 0) := by
    intro e he
    have hadj := (G.mem_interedges_iff.1 he).2.2
    by_cases h1 : e.1 ∈ A <;> by_cases h2 : e.2 ∈ A <;>
      simp only [f, G.mem_interedges_iff, mem_compl, h1, h2, hadj, ↓reduceIte,
        not_true_eq_false, not_false_eq_true, and_true, and_false, sub_self] <;> ring
  rw [sum_congr rfl hterm, ← mul_sum, sum_boundary_indicator]
  ring

/-- The two-valued test vector `a⁻¹` on `A` and `-b⁻¹` off `A`, where `0 < a ≤ b` are the
`w`-weights of `A` and `Aᶜ`: it is `w`-orthogonal to constants, has `w`-norm `a⁻¹ + b⁻¹`, and its
Rayleigh quotient is at most `2 * #E(A, Aᶜ) / a`. -/
private theorem twoVal_test {A : Finset V} {w : V → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hA : ∑ v ∈ A, w v = a) (hB : ∑ v ∈ Aᶜ, w v = b) :
    let f : V → ℝ := fun v => if v ∈ A then a⁻¹ else -b⁻¹
    ∑ v, f v * w v = 0 ∧ ∑ v, f v ^ 2 * w v = a⁻¹ + b⁻¹ ∧
      (f ⬝ᵥ (G.lapMatrix ℝ *ᵥ f)) / (a⁻¹ + b⁻¹) ≤ 2 * (#(G.interedges A Aᶜ) / a) := by
  intro f
  have hb : 0 < b := ha.trans_le hab
  have hsum : ∀ g : ℝ → ℝ, ∑ v, g (f v) * w v = g a⁻¹ * a + g (-b⁻¹) * b := fun g => by
    rw [← sum_add_sum_compl A, ← hA, ← hB, mul_sum, mul_sum]
    congr 1 <;> refine sum_congr rfl fun v hv => ?_
    · simp only [f, hv, ↓reduceIte, hA]
    · simp only [f, mem_compl.1 hv, ↓reduceIte, hB]
  refine ⟨(hsum fun x => x).trans (by simp only [inv_mul_cancel₀ ha.ne', neg_mul,
    inv_mul_cancel₀ hb.ne', add_neg_cancel]), (hsum (· ^ 2)).trans (by field_simp), ?_⟩
  have hinv : b⁻¹ ≤ a⁻¹ := inv_anti₀ ha hab
  rw [dotProduct_mulVec_lapMatrix_twoVal, sub_neg_eq_add, sq, ← mul_assoc,
    mul_div_cancel_right₀ _ (by positivity), div_eq_mul_inv]
  nlinarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ #(G.interedges A Aᶜ))]

/-- **Upper bound of Cheeger's inequality** ([Chung1997], §2.3, Lemma 2.1, p. 25):
`λ_G ≤ 2 h_G` for every finite simple graph `G`. -/
theorem normSpectralGap_le_two_mul_conductance :
    G.normSpectralGap ≤ 2 * G.conductance := by
  by_cases hbot : G = ⊥
  · rw [G.normSpectralGap_eq_zero_of_eq_bot hbot, G.conductance_eq_zero_of_eq_bot hbot, mul_zero]
  · have := nonempty_validCut_of_ne_bot G hbot
    rw [conductance, Real.mul_iInf_of_nonneg zero_le_two]
    refine le_ciInf fun ⟨A, hA_pos, hA_2⟩ => ?_
    have hcompl := G.vol_add_vol_compl A
    obtain ⟨horth, hdenom, hray⟩ := G.twoVal_test (A := A) (w := fun v => (G.degree v : ℝ))
      (b := G.vol Aᶜ) (Nat.cast_pos.2 hA_pos)
      (by exact_mod_cast (show G.vol A ≤ G.vol Aᶜ by omega))
      (by simp only [vol, Nat.cast_sum]) (by simp only [vol, Nat.cast_sum])
    refine (G.normSpectralGap_le_normRayleigh horth ?_).trans ?_
    · rw [hdenom]
      positivity
    · rwa [normRayleigh, hdenom]

/-- Helper rounding a single nonnegative half-vector `φ` with `0 < ∑ v, φ v ^ 2 * d_v` and
`2 * vol {v | 0 < φ v} ≤ vol(G)` to an upper level set `S` satisfying
`1 - √(1 - h_G(S)²) ≤ R_G(φ)`. -/
private theorem exists_level_cut_of_nonneg {φ : V → ℝ} (hφ : ∀ v, 0 ≤ φ v)
    (hpos : 0 < ∑ v, φ v ^ 2 * G.degree v)
    (hsupp : 2 * G.vol (univ.filter fun v => 0 < φ v) ≤ G.totalVol) :
    ∃ u : V,
      let S : Finset V := univ.filter fun v => G.degree v ≠ 0 ∧ φ u ≤ φ v
      0 < G.vol S ∧ 2 * G.vol S ≤ G.totalVol ∧
        1 - Real.sqrt (1 - G.setConductance S ^ 2) ≤ G.normRayleigh φ ∧
        G.setConductance S ≤ Real.sqrt (2 * G.normRayleigh φ) := by
  let φ₀ : V → ℝ := fun v => if G.degree v = 0 then 0 else φ v
  have hφ₀_nn : ∀ v, 0 ≤ φ₀ v := fun v => by
    simp only [φ₀]; split_ifs <;> [exact le_rfl; exact hφ v]
  have hN_eq : ∑ v, φ₀ v ^ 2 * G.degree v = ∑ v, φ v ^ 2 * G.degree v := by
    refine sum_congr rfl fun v _ => ?_
    by_cases hd : G.degree v = 0 <;> simp only [φ₀, hd, ↓reduceIte, Nat.cast_zero, mul_zero]
  have hD_eq : ∑ e ∈ G.interedges univ univ, (φ₀ e.1 - φ₀ e.2) ^ 2 =
      ∑ e ∈ G.interedges univ univ, (φ e.1 - φ e.2) ^ 2 := by
    refine sum_congr rfl fun e he => ?_
    have hadj := (G.mem_interedges_iff.1 he).2.2
    have h1 : G.degree e.1 ≠ 0 := ((G.degree_pos_iff_exists_adj e.1).2 ⟨e.2, hadj⟩).ne'
    have h2 : G.degree e.2 ≠ 0 := ((G.degree_pos_iff_exists_adj e.2).2 ⟨e.1, hadj.symm⟩).ne'
    simp only [φ₀, h1, h2, ↓reduceIte]
  have hray_eq : G.normRayleigh φ₀ = G.normRayleigh φ := by
    rw [normRayleigh, normRayleigh, G.dotProduct_mulVec_lapMatrix, G.dotProduct_mulVec_lapMatrix,
      hD_eq, hN_eq]
  have hN_pos : 0 < ∑ v, φ₀ v ^ 2 * G.degree v := hN_eq.symm ▸ hpos
  -- A vertex where `φ₀` is positive has positive degree, so `φ₀` agrees with `φ` there.
  have hdeg : ∀ {u}, 0 < φ₀ u → G.degree u ≠ 0 := fun {u} hu hd => by
    simp only [φ₀, hd, ↓reduceIte, lt_irrefl] at hu
  have hφ₀_eq : ∀ {u}, 0 < φ₀ u → φ₀ u = φ u := fun hu => by simp only [φ₀, hdeg hu, ↓reduceIte]
  set T₀ : Finset V := univ.filter fun v => 0 < φ₀ v
  have hT₀_ne : T₀.Nonempty := by
    obtain ⟨v, -, hv⟩ := exists_ne_zero_of_sum_ne_zero hN_pos.ne'
    refine ⟨v, mem_filter.2 ⟨mem_univ v, (hφ₀_nn v).lt_of_ne fun h => hv ?_⟩⟩
    rw [← h, zero_pow two_ne_zero, zero_mul]
  have hT₀_sub : T₀ ⊆ univ.filter fun v => 0 < φ v := fun v hv =>
    mem_filter.2 ⟨mem_univ v, hφ₀_eq (mem_filter.1 hv).2 ▸ (mem_filter.1 hv).2⟩
  let cutOf : V → Finset V := fun u => univ.filter fun v => φ₀ u ≤ φ₀ v
  have hcut_eq : ∀ u ∈ T₀, cutOf u = univ.filter fun v => G.degree v ≠ 0 ∧ φ u ≤ φ v := by
    intro u hu
    have hu_val : φ₀ u = φ u := hφ₀_eq (mem_filter.1 hu).2
    ext v
    simp only [cutOf, mem_filter, mem_univ, true_and, hu_val]
    by_cases hdv : G.degree v = 0
    · simp only [φ₀, hdv, ↓reduceIte, ne_eq, not_true_eq_false, false_and, iff_false, not_le]
      exact hu_val ▸ (mem_filter.1 hu).2
    · simp only [φ₀, hdv, ↓reduceIte, ne_eq, not_false_eq_true, true_and]
  have hcut_valid : ∀ u ∈ T₀, 0 < G.vol (cutOf u) ∧ 2 * G.vol (cutOf u) ≤ G.totalVol := by
    intro u hu
    have hu_pos : 0 < φ₀ u := (mem_filter.1 hu).2
    have hdu : 0 < G.degree u := Nat.pos_of_ne_zero (hdeg hu_pos)
    have hu_in : u ∈ cutOf u := mem_filter.2 ⟨mem_univ u, le_rfl⟩
    have hsub : cutOf u ⊆ T₀ := fun v hv =>
      mem_filter.2 ⟨mem_univ v, lt_of_lt_of_le hu_pos (mem_filter.1 hv).2⟩
    exact ⟨lt_of_lt_of_le hdu (G.vol_mono (singleton_subset_iff.2 hu_in)),
      (Nat.mul_le_mul_left 2 (G.vol_mono (hsub.trans hT₀_sub))).trans hsupp⟩
  obtain ⟨u_min, hu_min, hmin_cond⟩ :=
    T₀.exists_min_image (fun u => G.setConductance (cutOf u)) hT₀_ne
  set c := G.setConductance (cutOf u_min)
  have hc₀ : 0 ≤ c := by simp only [c, setConductance]; positivity
  have hlevel : ∀ u, 0 < φ₀ u →
      c * (∑ v with φ₀ u ≤ φ₀ v, (G.degree v : ℝ)) ≤
        #(G.interedges (cutOf u) (cutOf u)ᶜ) := by
    intro u hu_pos
    have huT : u ∈ T₀ := mem_filter.2 ⟨mem_univ u, hu_pos⟩
    obtain ⟨hv_pos, hv_2⟩ := hcut_valid u huT
    have hle_c : c ≤ G.setConductance (cutOf u) := hmin_cond u huT
    rw [G.setConductance_eq_of_two_mul_vol_le hv_2,
      le_div_iff₀ (Nat.cast_pos.2 hv_pos)] at hle_c
    simpa only [vol, Nat.cast_sum, cutOf] using hle_c
  have hquad := four_mul_sq_mul_sum_sq_le G hc₀ (fun v => (G.degree v : ℝ))
    (fun _ => Nat.cast_nonneg _) φ₀ hφ₀_nn hlevel
  set W := G.normRayleigh φ₀
  set N := ∑ v, φ₀ v ^ 2 * G.degree v
  have hD_W : ∑ e ∈ G.interedges univ univ, (φ₀ e.1 - φ₀ e.2) ^ 2 = 2 * W * N := by
    have hlap : φ₀ ⬝ᵥ (G.lapMatrix ℝ *ᵥ φ₀) = W * N := by
      simp only [W, normRayleigh, N, div_mul_cancel₀ _ hN_pos.ne']
    rw [G.dotProduct_mulVec_lapMatrix] at hlap
    linarith
  rw [hD_W] at hquad
  have hc_W : c ^ 2 ≤ W * (2 - W) := by
    have h4N : 0 < 4 * N ^ 2 := by positivity
    nlinarith
  have h1 : 1 - Real.sqrt (1 - c ^ 2) ≤ W := by
    linarith [le_abs_self (1 - W), Real.abs_le_sqrt (x := 1 - W) (y := 1 - c ^ 2) (by linarith)]
  have h2 : c ≤ Real.sqrt (2 * W) :=
    (le_abs_self c).trans (Real.abs_le_sqrt (by nlinarith [sq_nonneg W]))
  obtain ⟨hv_pos, hv_2⟩ := hcut_valid u_min hu_min
  refine ⟨u_min, ?_⟩
  dsimp only
  rw [← hcut_eq u_min hu_min, ← hray_eq]
  exact ⟨hv_pos, hv_2, h1, h2⟩

/-- Weighted median decomposition into a nonnegative half-vector `g v = max (d v) 0` (with
`d v = f v - m` or `d v = -(f v - m)`) whose positive support has `w`-weight at most half the total
weight and whose `w`-weighted Laplacian Rayleigh quotient is at most that of `f`. -/
private theorem exists_weighted_half_rayleigh_le {w f : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    (horth : ∑ v, f v * w v = 0) (hpos : 0 < ∑ v, f v ^ 2 * w v) :
    ∃ (m : ℝ) (d : V → ℝ),
      (d = (fun v => f v - m) ∨ d = (fun v => -(f v - m))) ∧
        2 * (∑ v with 0 < max (d v) 0, w v) ≤ ∑ v, w v ∧
        0 < ∑ v, max (d v) 0 ^ 2 * w v ∧
        ((fun v => max (d v) 0) ⬝ᵥ (G.lapMatrix ℝ *ᵥ fun v => max (d v) 0)) /
            (∑ v, max (d v) 0 ^ 2 * w v) ≤
          (f ⬝ᵥ (G.lapMatrix ℝ *ᵥ f)) / (∑ v, f v ^ 2 * w v) := by
  obtain ⟨m, hm_hi, hm_lo⟩ := exists_weighted_median w hw f
  let g_pos : V → ℝ := fun v => max (f v - m) 0
  let g_neg : V → ℝ := fun v => max (-(f v - m)) 0
  have hsupp_pos : 2 * (∑ v with 0 < g_pos v, w v) ≤ ∑ v, w v := by
    have heq : (univ.filter fun v => 0 < g_pos v) = univ.filter fun v => m < f v := by
      ext v
      simp only [g_pos, mem_filter, mem_univ, true_and, lt_max_iff, lt_irrefl, or_false, sub_pos]
    rwa [heq]
  have hsupp_neg : 2 * (∑ v with 0 < g_neg v, w v) ≤ ∑ v, w v := by
    have heq : (univ.filter fun v => 0 < g_neg v) = univ.filter fun v => f v < m := by
      ext v
      simp only [g_neg, mem_filter, mem_univ, true_and, lt_max_iff, lt_irrefl, or_false,
        neg_pos, sub_neg]
    rwa [heq]
  set N_pos := ∑ v, g_pos v ^ 2 * w v
  set N_neg := ∑ v, g_neg v ^ 2 * w v
  have hN_pos_nn : 0 ≤ N_pos := sum_nonneg fun v _ => mul_nonneg (sq_nonneg _) (hw v)
  have hN_neg_nn : 0 ≤ N_neg := sum_nonneg fun v _ => mul_nonneg (sq_nonneg _) (hw v)
  have hN_sum : ∑ v, f v ^ 2 * w v ≤ N_pos + N_neg := by
    have h1 : N_pos + N_neg = ∑ v, (f v - m) ^ 2 * w v := by
      simp only [N_pos, N_neg, g_pos, g_neg, ← sum_add_distrib, ← add_mul, sq_max_add_sq_max]
    have h2 : ∑ v, (f v - m) ^ 2 * w v =
        (∑ v, f v ^ 2 * w v) - 2 * m * (∑ v, f v * w v) + m ^ 2 * ∑ v, w v := by
      rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
      exact sum_congr rfl fun _ _ => by ring
    rw [h1, h2, horth]
    linarith [mul_nonneg (sq_nonneg m) (sum_nonneg (s := univ) fun v _ => hw v)]
  have hlap_sum : g_pos ⬝ᵥ (G.lapMatrix ℝ *ᵥ g_pos) + g_neg ⬝ᵥ (G.lapMatrix ℝ *ᵥ g_neg) ≤
      f ⬝ᵥ (G.lapMatrix ℝ *ᵥ f) := by
    rw [G.dotProduct_mulVec_lapMatrix, G.dotProduct_mulVec_lapMatrix, G.dotProduct_mulVec_lapMatrix,
      ← add_div, div_le_div_iff_of_pos_right zero_lt_two, ← sum_add_distrib]
    refine sum_le_sum fun e _ => ?_
    simpa only [g_pos, g_neg, sub_sub_sub_cancel_right] using
      sq_max_sub_max_add_sq_max_sub_max_le (f e.1 - m) (f e.2 - m)
  have hlap_pos_nn : 0 ≤ g_pos ⬝ᵥ (G.lapMatrix ℝ *ᵥ g_pos) := by
    rw [G.dotProduct_mulVec_lapMatrix]; positivity
  have hlap_neg_nn : 0 ≤ g_neg ⬝ᵥ (G.lapMatrix ℝ *ᵥ g_neg) := by
    rw [G.dotProduct_mulVec_lapMatrix]; positivity
  rcases hN_pos_nn.eq_or_lt with h0p | hgtp
  · have hgtn : 0 < N_neg := by linarith
    exact ⟨m, fun v => -(f v - m), Or.inr rfl, hsupp_neg, hgtn,
      (div_le_div_iff₀ hgtn hpos).2 (by nlinarith)⟩
  · rcases hN_neg_nn.eq_or_lt with h0n | hgtn
    · exact ⟨m, fun v => f v - m, Or.inl rfl, hsupp_pos, hgtp,
        (div_le_div_iff₀ hgtp hpos).2 (by nlinarith)⟩
    · by_cases hcmp : (g_pos ⬝ᵥ (G.lapMatrix ℝ *ᵥ g_pos)) / N_pos ≤
          (g_neg ⬝ᵥ (G.lapMatrix ℝ *ᵥ g_neg)) / N_neg
      · have hcross := (div_le_div_iff₀ hgtp hgtn).1 hcmp
        exact ⟨m, fun v => f v - m, Or.inl rfl, hsupp_pos, hgtp,
          (div_le_div_iff₀ hgtp hpos).2 (by nlinarith)⟩
      · push Not at hcmp
        have hcross := (div_lt_div_iff₀ hgtn hgtp).1 hcmp
        exact ⟨m, fun v => -(f v - m), Or.inr rfl, hsupp_neg, hgtn,
          (div_le_div_iff₀ hgtn hpos).2 (by nlinarith)⟩

/-- **Explicit sweep-cut rounding** ([Chung1997], §2.3, proof of Theorems 2.2 and 2.3, pp. 26–28):
for every `f : V → ℝ` with `∑ v, f v * d_v = 0` and `0 < ∑ v, f v ^ 2 * d_v`, there exists an
explicit threshold cut `S` (either `{v | d_v ≠ 0 ∧ t ≤ f v}` or `{v | d_v ≠ 0 ∧ f v ≤ t}`) with
`0 < vol(S)`, `2 * vol(S) ≤ vol(G)`, `1 - √(1 - h_G(S)²) ≤ R_G(f)`, and `h_G(S) ≤ √(2 R_G(f))`. -/
theorem exists_sweep_cut_le {f : V → ℝ} (horth : ∑ v, f v * G.degree v = 0)
    (hpos : 0 < ∑ v, f v ^ 2 * G.degree v) :
    ∃ S : Finset V,
      ((∃ t : ℝ, S = univ.filter fun v => G.degree v ≠ 0 ∧ t ≤ f v) ∨
        ∃ t : ℝ, S = univ.filter fun v => G.degree v ≠ 0 ∧ f v ≤ t) ∧
      0 < G.vol S ∧ 2 * G.vol S ≤ G.totalVol ∧
      1 - Real.sqrt (1 - G.setConductance S ^ 2) ≤ G.normRayleigh f ∧
      G.setConductance S ≤ Real.sqrt (2 * G.normRayleigh f) := by
  obtain ⟨m, d, hd_cases, hsupp_real, hgt, hray_le⟩ :=
    exists_weighted_half_rayleigh_le G (fun _ => Nat.cast_nonneg _) horth hpos
  have hsupp : 2 * G.vol (univ.filter fun v => 0 < max (d v) 0) ≤ G.totalVol := by
    exact_mod_cast (by simpa only [vol, totalVol, Nat.cast_sum] using hsupp_real :
      (2 * G.vol (univ.filter fun v => 0 < max (d v) 0) : ℝ) ≤ G.totalVol)
  rw [← normRayleigh, ← normRayleigh] at hray_le
  obtain ⟨u, hv_pos, hv_2, h1, h2⟩ :=
    exists_level_cut_of_nonneg G (fun _ => le_max_right _ _) hgt hsupp
  set S : Finset V := univ.filter fun v => G.degree v ≠ 0 ∧ max (d u) 0 ≤ max (d v) 0
  have hdu_pos : 0 < d u := by
    by_contra hle
    have hdu : max (d u) 0 = 0 := max_eq_right (not_lt.1 hle)
    have hS_all : S = univ.filter fun v => G.degree v ≠ 0 := by
      ext v
      simp only [S, hdu, mem_filter, mem_univ, true_and, and_iff_left (le_max_right _ _)]
    have hS_vol : G.vol S = G.totalVol := by
      simp only [vol, totalVol, hS_all]
      refine sum_subset (subset_univ _) fun v _ hv => ?_
      simp only [mem_filter, mem_univ, true_and, not_not] at hv
      exact hv
    omega
  have hs : S = univ.filter fun v => G.degree v ≠ 0 ∧ d u ≤ d v := by
    have hdu : max (d u) 0 = d u := max_eq_left hdu_pos.le
    ext v
    simp only [S, hdu, mem_filter, mem_univ, true_and, le_max_iff]
    exact and_congr_right fun _ =>
      ⟨fun h => by rcases h with h | h <;> linarith, fun h => Or.inl h⟩
  rcases hd_cases with rfl | rfl
  · exact ⟨S, Or.inl ⟨f u, by simpa only [sub_le_sub_iff_right] using hs⟩, hv_pos, hv_2,
      h1.trans hray_le, h2.trans (Real.sqrt_le_sqrt (by linarith))⟩
  · exact ⟨S, Or.inr ⟨f u, by simpa only [neg_le_neg_iff, sub_le_sub_iff_right] using hs⟩,
      hv_pos, hv_2, h1.trans hray_le, h2.trans (Real.sqrt_le_sqrt (by linarith))⟩

/-- **Strengthened Cheeger lower bound** ([Chung1997], §2.3, Theorem 2.3, p. 27):
`1 - √(1 - h_G²) ≤ λ_G` for every finite simple graph `G`. -/
theorem one_sub_sqrt_one_sub_conductance_sq_le_normSpectralGap :
    1 - Real.sqrt (1 - G.conductance ^ 2) ≤ G.normSpectralGap := by
  by_cases hbot : G = ⊥
  · rw [G.conductance_eq_zero_of_eq_bot hbot, G.normSpectralGap_eq_zero_of_eq_bot hbot]
    simp only [zero_pow two_ne_zero, sub_zero, Real.sqrt_one, sub_self, le_rfl]
  · refine (G.le_normSpectralGap_iff hbot).2 fun f horth hpos => ?_
    obtain ⟨S, -, hv_pos, hv_2, h1, -⟩ := G.exists_sweep_cut_le horth hpos
    have hcompl := G.vol_add_vol_compl S
    have hc_le : G.conductance ≤ G.setConductance S :=
      G.conductance_le_setConductance (by omega)
    have hsq_le : G.conductance ^ 2 ≤ G.setConductance S ^ 2 :=
      pow_le_pow_left₀ G.conductance_nonneg hc_le 2
    have hsqrt_ge : Real.sqrt (1 - G.setConductance S ^ 2) ≤ Real.sqrt (1 - G.conductance ^ 2) :=
      Real.sqrt_le_sqrt (by linarith)
    linarith

/-- **Cheeger lower bound** ([Chung1997], §2.3, Theorem 2.2, p. 26):
`h_G² / 2 ≤ λ_G` for every finite simple graph `G`. -/
theorem conductance_sq_div_two_le_normSpectralGap :
    G.conductance ^ 2 / 2 ≤ G.normSpectralGap := by
  have hc0 : 0 ≤ G.conductance := G.conductance_nonneg
  have hc1 : G.conductance ≤ 1 := G.conductance_le_one
  have h1_sub_nn : 0 ≤ 1 - G.conductance ^ 2 / 2 := by nlinarith
  have hsqrt : Real.sqrt (1 - G.conductance ^ 2) ≤ 1 - G.conductance ^ 2 / 2 := by
    rw [Real.sqrt_le_iff]
    exact ⟨h1_sub_nn, by nlinarith [sq_nonneg (G.conductance ^ 2)]⟩
  linarith [G.one_sub_sqrt_one_sub_conductance_sq_le_normSpectralGap]

/-- **Strict Cheeger lower bound** ([Chung1997], §2.3, Theorem 2.2, pp. 26–27):
whenever `0 < h_G`, `h_G² / 2 < λ_G`. -/
theorem conductance_sq_div_two_lt_normSpectralGap (hpos : 0 < G.conductance) :
    G.conductance ^ 2 / 2 < G.normSpectralGap := by
  have hc1 : G.conductance ≤ 1 := G.conductance_le_one
  have h1_sub_pos : 0 < 1 - G.conductance ^ 2 / 2 := by nlinarith
  have hsqrt : Real.sqrt (1 - G.conductance ^ 2) < 1 - G.conductance ^ 2 / 2 := by
    refine (Real.sqrt_lt' h1_sub_pos).2 ?_
    have hpow4 : 0 < G.conductance ^ 4 := by positivity
    nlinarith
  linarith [G.one_sub_sqrt_one_sub_conductance_sq_le_normSpectralGap]

/-- **Strict Cheeger lower bound for connected graphs** ([Chung1997], §2.3, Theorem 2.2, p. 26):
for any connected graph `G` on at least two vertices, `h_G² / 2 < λ_G`. -/
theorem conductance_sq_div_two_lt_normSpectralGap_of_connected [Nontrivial V]
    (hconn : G.Connected) :
    G.conductance ^ 2 / 2 < G.normSpectralGap := by
  have hiso : ∀ v, 0 < G.degree v := fun v => by
    obtain ⟨w, hvw⟩ := exists_ne v
    obtain ⟨p⟩ := hconn v w
    rcases p with _ | @⟨_, x, _, hadj, _⟩
    · exact absurd rfl hvw.symm
    · exact (G.degree_pos_iff_exists_adj v).2 ⟨x, hadj⟩
  exact G.conductance_sq_div_two_lt_normSpectralGap ((G.connected_iff_conductance_pos hiso).1 hconn)

/-- On at least two vertices with no isolated vertices, `G` is connected iff `0 < λ_G`
([Chung1997], Lemma 1.7(iv), p. 7). -/
theorem connected_iff_normSpectralGap_pos [Nontrivial V] (hiso : ∀ v, 0 < G.degree v) :
    G.Connected ↔ 0 < G.normSpectralGap := by
  rw [G.connected_iff_conductance_pos hiso]
  refine ⟨fun h => lt_of_le_of_lt (by positivity) (G.conductance_sq_div_two_lt_normSpectralGap h),
    fun h => ?_⟩
  have hle := G.normSpectralGap_le_two_mul_conductance
  linarith

end NormalizedCheeger

/-! ### Combinatorial Laplacian (`h'_G` and `λ'_1`, [Chung1997], §2.5; [AlonMilman1985]) -/

section CombinatorialCheeger

variable [DecidableEq V]

/-- **Isoperimetric number (modified Cheeger constant)**
`h'_G = inf_{0 < |S| ≤ |V| / 2} |E(S, Sᶜ)| / |S|` ([Chung1997], §2.5, p. 34; [AlonMilman1985]).
Equals `0` when `|V| ≤ 1`. -/
noncomputable def isoperimetricNum : ℝ :=
  ⨅ S : {S : Finset V // S.Nonempty ∧ 2 * #S ≤ Fintype.card V},
    (#(G.interedges S.val S.valᶜ) : ℝ) / #S.val

theorem isoperimetricNum_def :
    G.isoperimetricNum =
      ⨅ S : {S : Finset V // S.Nonempty ∧ 2 * #S ≤ Fintype.card V},
        (#(G.interedges S.val S.valᶜ) : ℝ) / #S.val := by
  rfl

/-- **Algebraic connectivity (Fiedler value)** `λ'_1 = inf_{∑ f = 0, f ≠ 0} (f ⬝ᵥ L f) / (f ⬝ᵥ f)`
([Chung1997], §2.5, p. 34; [AlonMilman1985]). Equals `0` when `|V| ≤ 1`. -/
noncomputable def algConnectivity : ℝ :=
  ⨅ f : {f : V → ℝ // ∑ v, f v = 0 ∧ ∃ v, f v ≠ 0},
    (f.val ⬝ᵥ (G.lapMatrix ℝ *ᵥ f.val)) / (f.val ⬝ᵥ f.val)

theorem algConnectivity_def :
    G.algConnectivity =
      ⨅ f : {f : V → ℝ // ∑ v, f v = 0 ∧ ∃ v, f v ≠ 0},
        (f.val ⬝ᵥ (G.lapMatrix ℝ *ᵥ f.val)) / (f.val ⬝ᵥ f.val) := by
  rfl

theorem isoperimetricNum_nonneg : 0 ≤ G.isoperimetricNum := by
  exact Real.iInf_nonneg fun _ => by positivity

theorem algConnectivity_nonneg : 0 ≤ G.algConnectivity := by
  exact Real.iInf_nonneg fun ⟨f, _, _⟩ => by
    rw [G.dotProduct_mulVec_lapMatrix]
    exact div_nonneg (div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) zero_le_two)
      (sum_nonneg fun v _ => mul_self_nonneg (f v))

theorem isoperimetricNum_eq_zero_of_subsingleton [Subsingleton V] : G.isoperimetricNum = 0 := by
  have : IsEmpty {S : Finset V // S.Nonempty ∧ 2 * #S ≤ Fintype.card V} :=
    ⟨fun ⟨S, hne, h2⟩ => by
      have := Fintype.card_le_one_iff_subsingleton.2 ‹_›
      have := hne.card_pos
      omega⟩
  exact Real.iInf_of_isEmpty _

theorem algConnectivity_eq_zero_of_subsingleton [Subsingleton V] : G.algConnectivity = 0 := by
  have : IsEmpty {f : V → ℝ // ∑ v, f v = 0 ∧ ∃ v, f v ≠ 0} :=
    ⟨fun ⟨f, hsum, v, hv⟩ => by
      have hall : univ = ({v} : Finset V) := by ext w; simp [Subsingleton.elim w v]
      rw [hall, sum_singleton] at hsum
      exact hv hsum⟩
  exact Real.iInf_of_isEmpty _

theorem isoperimetricNum_mul_card_le {S : Finset V} (h2 : 2 * #S ≤ Fintype.card V) :
    G.isoperimetricNum * #S ≤ #(G.interedges S Sᶜ) := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · rw [card_empty, Nat.cast_zero, mul_zero]; exact Nat.cast_nonneg _
  · have hb : BddBelow (Set.range
        fun S : {S : Finset V // S.Nonempty ∧ 2 * #S ≤ Fintype.card V} =>
          (#(G.interedges S.val S.valᶜ) : ℝ) / #S.val) :=
      ⟨0, Set.forall_mem_range.2 fun _ => by positivity⟩
    rw [← le_div_iff₀ (Nat.cast_pos.2 hne.card_pos)]
    exact ciInf_le hb ⟨S, hne, h2⟩

theorem le_isoperimetricNum_iff [Nontrivial V] {c : ℝ} :
    c ≤ G.isoperimetricNum ↔
      ∀ S : Finset V, S.Nonempty → 2 * #S ≤ Fintype.card V →
        c * #S ≤ #(G.interedges S Sᶜ) := by
  obtain ⟨v₀⟩ := (inferInstance : Nonempty V)
  have : Nonempty {S : Finset V // S.Nonempty ∧ 2 * #S ≤ Fintype.card V} :=
    ⟨⟨{v₀}, singleton_nonempty v₀, by rw [card_singleton, mul_one]; exact Fintype.one_lt_card⟩⟩
  refine ⟨fun h S _ h2 => (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _)).trans
      (G.isoperimetricNum_mul_card_le h2),
    fun h => ?_⟩
  rw [isoperimetricNum]
  exact le_ciInf fun ⟨S, hne, h2⟩ => (le_div_iff₀ (Nat.cast_pos.2 hne.card_pos)).2 (h S hne h2)

theorem algConnectivity_le_rayleigh {f : V → ℝ} (horth : ∑ v, f v = 0) (hne : ∃ v, f v ≠ 0) :
    G.algConnectivity ≤ (f ⬝ᵥ (G.lapMatrix ℝ *ᵥ f)) / (f ⬝ᵥ f) := by
  have hb : BddBelow (Set.range fun g : {f : V → ℝ // ∑ v, f v = 0 ∧ ∃ v, f v ≠ 0} =>
      (g.val ⬝ᵥ (G.lapMatrix ℝ *ᵥ g.val)) / (g.val ⬝ᵥ g.val)) :=
    ⟨0, Set.forall_mem_range.2 fun ⟨g, _, _⟩ => by
      rw [G.dotProduct_mulVec_lapMatrix]
      exact div_nonneg (div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) zero_le_two)
        (sum_nonneg fun v _ => mul_self_nonneg (g v))⟩
  exact ciInf_le hb ⟨f, horth, hne⟩

/-- **Combinatorial Cheeger upper bound** ([Chung1997], §2.5, p. 35; [AlonMilman1985]):
`λ'_1 ≤ 2 h'_G` for every finite simple graph `G`. -/
theorem algConnectivity_le_two_mul_isoperimetricNum :
    G.algConnectivity ≤ 2 * G.isoperimetricNum := by
  rcases subsingleton_or_nontrivial V with hsub | hnt
  · simp only [G.algConnectivity_eq_zero_of_subsingleton,
      G.isoperimetricNum_eq_zero_of_subsingleton, mul_zero, le_rfl]
  · obtain ⟨v₀⟩ := (inferInstance : Nonempty V)
    have : Nonempty {S : Finset V // S.Nonempty ∧ 2 * #S ≤ Fintype.card V} :=
      ⟨⟨{v₀}, singleton_nonempty v₀, by rw [card_singleton, mul_one]; exact Fintype.one_lt_card⟩⟩
    rw [isoperimetricNum, Real.mul_iInf_of_nonneg zero_le_two]
    refine le_ciInf fun ⟨A, hA_ne, hA_2⟩ => ?_
    have hcompl := card_add_card_compl A
    obtain ⟨uA, huA⟩ := hA_ne
    obtain ⟨horth, hdenom, hray⟩ := G.twoVal_test (A := A) (w := fun _ => 1) (b := #Aᶜ)
      (Nat.cast_pos.2 (card_pos.2 ⟨uA, huA⟩)) (by exact_mod_cast (show #A ≤ #Aᶜ by omega))
      (by simp only [sum_const, nsmul_one]) (by simp only [sum_const, nsmul_one])
    simp only [mul_one] at horth hdenom
    refine (G.algConnectivity_le_rayleigh horth ⟨uA, ?_⟩).trans (Eq.trans_le ?_ hray)
    · simpa only [huA, ↓reduceIte, ne_eq, inv_eq_zero, Nat.cast_eq_zero, card_eq_zero]
        using ne_empty_of_mem huA
    · rw [← hdenom]
      congr 1
      simp only [dotProduct, sq]

/-- **Explicit cardinality sweep-cut rounding** ([Chung1997], §2.5, p. 35; [AlonMilman1985]):
for every nonzero `f : V → ℝ` with `∑ v, f v = 0`, there is a sweep threshold cut `S`
(`{v | t ≤ f v}` or `{v | f v ≤ t}`) with `S.Nonempty`, `2 * #S ≤ Fintype.card V`, and
`(#(G.interedges S Sᶜ) / #S : ℝ) ^ 2 ≤ 2 * G.maxDegree * ((f ⬝ᵥ (G.lapMatrix ℝ *ᵥ f)) / (f ⬝ᵥ f))`.
-/
theorem exists_card_sweep_cut_le {f : V → ℝ} (horth : ∑ v, f v = 0) (hne : ∃ v, f v ≠ 0) :
    ∃ S : Finset V,
      ((∃ t : ℝ, S = univ.filter fun v => t ≤ f v) ∨
        ∃ t : ℝ, S = univ.filter fun v => f v ≤ t) ∧
      S.Nonempty ∧ 2 * #S ≤ Fintype.card V ∧
      ((#(G.interedges S Sᶜ) : ℝ) / #S) ^ 2 ≤
        2 * G.maxDegree * ((f ⬝ᵥ (G.lapMatrix ℝ *ᵥ f)) / (f ⬝ᵥ f)) := by
  obtain ⟨v_ne, hv_ne⟩ := hne
  have hnorm_pos : 0 < f ⬝ᵥ f := by
    change 0 < ∑ v, f v * f v
    exact lt_of_lt_of_le (mul_self_pos.2 hv_ne)
      (single_le_sum (fun v _ => mul_self_nonneg (f v)) (mem_univ v_ne))
  have horth1 : ∑ v, f v * (1 : ℝ) = 0 := by simpa only [mul_one] using horth
  have hsq_eq : ∑ v, f v ^ 2 = f ⬝ᵥ f := sum_congr rfl fun _ _ => sq _
  have hsq1_pos : 0 < ∑ v, f v ^ 2 * (1 : ℝ) := by
    simpa only [mul_one, hsq_eq] using hnorm_pos
  obtain ⟨m, d, hd_cases, hsupp1, hgt1, hray1⟩ :=
    exists_weighted_half_rayleigh_le G (fun _ => zero_le_one) horth1 hsq1_pos
  simp only [mul_one, sum_const, card_univ, nsmul_eq_mul] at hsupp1 hgt1 hray1
  rw [hsq_eq] at hray1
  have hsupp : 2 * #{v | 0 < max (d v) 0} ≤ Fintype.card V := by exact_mod_cast hsupp1
  set φ : V → ℝ := fun v => max (d v) 0
  change ((φ ⬝ᵥ (G.lapMatrix ℝ *ᵥ φ)) / ∑ v, φ v ^ 2 ≤
    (f ⬝ᵥ (G.lapMatrix ℝ *ᵥ f)) / (f ⬝ᵥ f)) at hray1
  set T := univ.filter fun v => 0 < φ v
  have hT_ne : T.Nonempty := by
    obtain ⟨v, -, hv⟩ := exists_ne_zero_of_sum_ne_zero hgt1.ne'
    exact ⟨v, mem_filter.2 ⟨mem_univ v,
      (le_max_right _ _).lt_of_ne ((pow_ne_zero_iff two_ne_zero).mp hv).symm⟩⟩
  let cutOf : V → Finset V := fun u => univ.filter fun v => φ u ≤ φ v
  obtain ⟨u_min, hu_min, hmin_c⟩ :=
    T.exists_min_image (fun u => (#(G.interedges (cutOf u) (cutOf u)ᶜ) : ℝ) / #(cutOf u)) hT_ne
  have hu_pos : 0 < φ u_min := (mem_filter.1 hu_min).2
  set c := (#(G.interedges (cutOf u_min) (cutOf u_min)ᶜ) : ℝ) / #(cutOf u_min)
  have hc₀ : 0 ≤ c := by simp only [c]; positivity
  have hlevel : ∀ u, 0 < φ u →
      c * (∑ v with φ u ≤ φ v, (1 : ℝ)) ≤ #(G.interedges (cutOf u) (cutOf u)ᶜ) := by
    intro u hu
    have huT : u ∈ T := mem_filter.2 ⟨mem_univ u, hu⟩
    have hne_u : (cutOf u).Nonempty := ⟨u, mem_filter.2 ⟨mem_univ u, le_rfl⟩⟩
    have hle := (le_div_iff₀ (Nat.cast_pos.2 hne_u.card_pos)).1 (hmin_c u huT)
    simpa only [sum_const, nsmul_eq_mul, mul_one, cutOf] using hle
  have hquad := four_mul_sq_mul_sum_sq_le G hc₀ (fun _ => (1 : ℝ)) (fun _ => zero_le_one)
    φ (fun _ => le_max_right _ _) hlevel
  simp only [mul_one] at hquad
  have hdeg_le : ∑ v, φ v ^ 2 * G.degree v ≤ G.maxDegree * ∑ v, φ v ^ 2 := by
    rw [mul_sum]
    refine sum_le_sum fun v _ => ?_
    rw [mul_comm (G.maxDegree : ℝ)]
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.2 (G.degree_le_maxDegree v)) (sq_nonneg _)
  set D := ∑ e ∈ G.interedges univ univ, (φ e.1 - φ e.2) ^ 2
  have hD_nn : 0 ≤ D := sum_nonneg fun _ _ => sq_nonneg _
  have hrhs_le : D * (4 * (∑ v, φ v ^ 2 * G.degree v) - D) ≤
      D * (4 * G.maxDegree * ∑ v, φ v ^ 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hD_nn
  have hcomb := hquad.trans hrhs_le
  have hlap_D : D = 2 * (φ ⬝ᵥ (G.lapMatrix ℝ *ᵥ φ)) := by
    rw [G.dotProduct_mulVec_lapMatrix]; ring
  rw [hlap_D] at hcomb
  have hc_bound : c ^ 2 ≤ 2 * G.maxDegree * ((f ⬝ᵥ (G.lapMatrix ℝ *ᵥ f)) / (f ⬝ᵥ f)) := by
    have hc_φ : c ^ 2 ≤ 2 * G.maxDegree * ((φ ⬝ᵥ (G.lapMatrix ℝ *ᵥ φ)) / ∑ v, φ v ^ 2) := by
      rw [mul_div_assoc', le_div_iff₀ hgt1]
      have h4 : 0 < 4 * ∑ v, φ v ^ 2 := by positivity
      nlinarith
    exact hc_φ.trans (mul_le_mul_of_nonneg_left hray1 (by positivity))
  have hsub_u : cutOf u_min ⊆ T := fun v hv =>
    mem_filter.2 ⟨mem_univ v, lt_of_lt_of_le hu_pos (mem_filter.1 hv).2⟩
  have hne_S : (cutOf u_min).Nonempty := ⟨u_min, mem_filter.2 ⟨mem_univ u_min, le_rfl⟩⟩
  have h2_S : 2 * #(cutOf u_min) ≤ Fintype.card V :=
    (Nat.mul_le_mul_left 2 (card_le_card hsub_u)).trans hsupp
  have hdu_pos : 0 < d u_min := by
    simpa only [φ, lt_max_iff, lt_irrefl, or_false] using hu_pos
  have hS_eq : cutOf u_min = univ.filter fun v => d u_min ≤ d v := by
    have hgu : φ u_min = d u_min := max_eq_left hdu_pos.le
    ext v
    simp only [cutOf, hgu, φ, mem_filter, mem_univ, true_and, le_max_iff]
    exact ⟨fun h => by rcases h with h | h <;> linarith, fun h => Or.inl h⟩
  refine ⟨cutOf u_min, ?_, hne_S, h2_S, hc_bound⟩
  rcases hd_cases with rfl | rfl
  · exact Or.inl ⟨f u_min, by simpa only [sub_le_sub_iff_right] using hS_eq⟩
  · exact Or.inr ⟨f u_min, by simpa only [neg_le_neg_iff, sub_le_sub_iff_right] using hS_eq⟩

omit [DecidableEq V] G [DecidableRel G.Adj] in
private theorem nonempty_zeroSum_of_nontrivial [Nontrivial V] :
    Nonempty {f : V → ℝ // ∑ v, f v = 0 ∧ ∃ v, f v ≠ 0} := by
  classical
  obtain ⟨u₀, w₀, huw₀⟩ := exists_pair_ne V
  let f₀ : V → ℝ := fun v => if v = u₀ then 1 else if v = w₀ then -1 else 0
  have hf₀_sum : ∑ v, f₀ v = 0 := by
    have hsub : ∑ v, f₀ v = ∑ v ∈ ({u₀, w₀} : Finset V), f₀ v := by
      refine (sum_subset (subset_univ _) fun v _ hv => ?_).symm
      rw [mem_insert, mem_singleton, not_or] at hv
      simp only [f₀, hv.1, hv.2, ↓reduceIte]
    rw [hsub, sum_pair huw₀]
    simp only [f₀, huw₀.symm, ↓reduceIte, add_neg_cancel]
  exact ⟨⟨f₀, hf₀_sum, u₀, by simp only [f₀, ↓reduceIte]; exact one_ne_zero⟩⟩

/-- **Combinatorial Cheeger lower bound (product form)** ([Chung1997], §2.5, p. 35;
[AlonMilman1985]): `(h'_G)² ≤ 2 Δ λ'_1` for every finite simple graph `G`. -/
theorem isoperimetricNum_sq_le_two_mul_maxDegree_mul_algConnectivity :
    G.isoperimetricNum ^ 2 ≤ 2 * G.maxDegree * G.algConnectivity := by
  rcases subsingleton_or_nontrivial V with hsub | hnt
  · simp only [G.isoperimetricNum_eq_zero_of_subsingleton,
      G.algConnectivity_eq_zero_of_subsingleton, zero_pow two_ne_zero, mul_zero, le_rfl]
  · have := nonempty_zeroSum_of_nontrivial (V := V)
    rw [algConnectivity, Real.mul_iInf_of_nonneg (by positivity)]
    refine le_ciInf fun ⟨f, horth, hne⟩ => ?_
    obtain ⟨S, -, hne_S, h2_S, hc_S⟩ := G.exists_card_sweep_cut_le horth hne
    have hle_iso : G.isoperimetricNum ≤ (#(G.interedges S Sᶜ) : ℝ) / #S :=
      (le_div_iff₀ (Nat.cast_pos.2 hne_S.card_pos)).2 (G.isoperimetricNum_mul_card_le h2_S)
    exact (pow_le_pow_left₀ G.isoperimetricNum_nonneg hle_iso 2).trans hc_S

/-- **Combinatorial Cheeger lower bound (ratio form)** ([Chung1997], §2.5, p. 35; [AlonMilman1985]):
when `0 < G.maxDegree`, `(h'_G)² / (2 Δ) ≤ λ'_1`. -/
theorem isoperimetricNum_sq_div_two_mul_maxDegree_le_algConnectivity (hd : 0 < G.maxDegree) :
    G.isoperimetricNum ^ 2 / (2 * G.maxDegree) ≤ G.algConnectivity :=
  (div_le_iff₀ (by positivity)).2
    (by simpa only [mul_comm (2 * (G.maxDegree : ℝ))] using
      G.isoperimetricNum_sq_le_two_mul_maxDegree_mul_algConnectivity)

/-- For a `d`-regular graph with `0 < d`, `h_G = h'_G / d`. -/
theorem IsRegularOfDegree.conductance_eq {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
    (hd : G.IsRegularOfDegree d) (hd_pos : 0 < d) :
    G.conductance = G.isoperimetricNum / d := by
  rcases subsingleton_or_nontrivial V with hsub | hnt
  · have hbot : G = ⊥ := by
      ext u v
      simp only [Subsingleton.elim u v, G.loopless.irrefl, bot_adj]
    rw [G.conductance_eq_zero_of_eq_bot hbot, G.isoperimetricNum_eq_zero_of_subsingleton, zero_div]
  · have htot : G.totalVol = d * Fintype.card V := by
      simpa only [totalVol, card_univ] using hd.vol_eq univ
    have hd_real : (0 : ℝ) < d := Nat.cast_pos.2 hd_pos
    obtain ⟨v₀⟩ := (inferInstance : Nonempty V)
    obtain ⟨w₀, hvw₀⟩ := (G.degree_pos_iff_exists_adj v₀).1 (hd.degree_eq v₀ ▸ hd_pos)
    have hne_bot : G ≠ ⊥ := fun h => by rw [h] at hvw₀; exact hvw₀
    refine le_antisymm ?_ ((G.le_conductance_iff hne_bot).2 fun S _ h2 => ?_)
    · rw [le_div_iff₀ hd_real]
      refine G.le_isoperimetricNum_iff.2 fun S _ h2 => ?_
      have h := G.conductance_mul_vol_le (S := S)
        (by rw [hd.vol_eq, htot, Nat.mul_left_comm]; exact Nat.mul_le_mul_left d h2)
      rw [hd.vol_eq, Nat.cast_mul] at h
      linarith
    · rw [hd.vol_eq, htot, Nat.mul_left_comm] at h2
      have h := G.isoperimetricNum_mul_card_le (Nat.le_of_mul_le_mul_left h2 hd_pos)
      rw [hd.vol_eq, Nat.cast_mul, div_mul_eq_mul_div, div_le_iff₀ hd_real]
      nlinarith

/-- For a `d`-regular graph with `0 < d`, `λ_G = λ'_1 / d`. -/
theorem IsRegularOfDegree.normSpectralGap_eq {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
    (hd : G.IsRegularOfDegree d) (hd_pos : 0 < d) :
    G.normSpectralGap = G.algConnectivity / d := by
  rcases subsingleton_or_nontrivial V with hsub | hnt
  · have hbot : G = ⊥ := by
      ext u v
      simp only [Subsingleton.elim u v, G.loopless.irrefl, bot_adj]
    rw [G.normSpectralGap_eq_zero_of_eq_bot hbot, G.algConnectivity_eq_zero_of_subsingleton,
      zero_div]
  · have hd_real : (0 : ℝ) < d := Nat.cast_pos.2 hd_pos
    obtain ⟨v₀⟩ := (inferInstance : Nonempty V)
    obtain ⟨w₀, hvw₀⟩ := (G.degree_pos_iff_exists_adj v₀).1 (hd.degree_eq v₀ ▸ hd_pos)
    have hne_bot : G ≠ ⊥ := fun h => by rw [h] at hvw₀; exact hvw₀
    have := nonempty_orthog_of_ne_bot G hne_bot
    have := nonempty_zeroSum_of_nontrivial (V := V)
    have hray : ∀ f : V → ℝ,
        G.normRayleigh f = (f ⬝ᵥ (G.lapMatrix ℝ *ᵥ f)) / (f ⬝ᵥ f) / d := fun f => by
      simp only [normRayleigh, hd.degree_eq, ← sum_mul, div_div, dotProduct, sq]
    refine le_antisymm ?_ ((G.le_normSpectralGap_iff hne_bot).2 fun f horth_d hpos_d => ?_)
    · rw [le_div_iff₀ hd_real]
      refine le_ciInf fun ⟨f, horth, v_ne, hv_ne⟩ => ?_
      have hle := G.normSpectralGap_le_normRayleigh (f := f)
        (by simp only [hd.degree_eq, ← sum_mul, horth, zero_mul])
        (by simp only [hd.degree_eq, ← sum_mul]
            exact mul_pos (lt_of_lt_of_le (sq_pos_of_ne_zero hv_ne)
              (single_le_sum (fun v _ => sq_nonneg (f v)) (mem_univ v_ne))) hd_real)
      rwa [hray, le_div_iff₀ hd_real] at hle
    · simp only [hd.degree_eq, ← sum_mul] at horth_d hpos_d
      have horth : ∑ v, f v = 0 := (mul_eq_zero.1 horth_d).resolve_right hd_real.ne'
      have hne : ∃ v, f v ≠ 0 := by
        by_contra! hall
        simp only [hall, zero_pow two_ne_zero, sum_const_zero, zero_mul, lt_irrefl] at hpos_d
      rw [hray]
      exact div_le_div_of_nonneg_right (G.algConnectivity_le_rayleigh horth hne) hd_real.le

end CombinatorialCheeger

end SimpleGraph
