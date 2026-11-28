/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.PACLearning.DualVCDimension
public import CslibFrontier.MachineLearning.PACLearning.GrowthFunction
public import Mathlib.InformationTheory.Hamming
import CslibFrontier.MachineLearning.PACLearning.Packing
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Haussler's Sphere-Packing Lemma for VC Classes

Subsampling alone bounds an `ε`-separated set of labelings of VC dimension `d` by Dudley's
`O((1 / ε) ^ (2 d))` (`card_le_div_pow_of_le_hammingDist` in
`CslibFrontier/MachineLearning/PACLearning/Packing.lean`), losing a factor of `2` in the exponent.
Haussler [Haussler1995] sharpened the exponent to the optimal `d`, proving that every `ε`-separated
subset `P ⊆ {0, 1}^m` whose shattered sets have size at most `d` satisfies

`|P| ≤ e (d + 1) (2 e / ε) ^ d`.

This module formalizes Haussler's sphere-packing bound and its Hamming covering-net corollary:

1. **Weighted one-inclusion shifting inequality** (`sum_min_update_le_mul_sum`): a weighted
   coordinate-shifting strengthening of the hypercube edge-density bound in [Haussler1995]. For any
   nonnegative weight `μ : (ι → Bool) → ℝ` whose positive support shatters no finite set of more
   than `d` coordinates, the sum of `min (μ f) (μ (update f i true))` over all hypercube edges is
   at most `d · ∑ f, μ f`. Coordinate shifting replaces `μ` on `Fin (n + 1) → Bool` by pointwise
   `max` and `min` across coordinate `0`, whose supports shatter at most `d` and `d - 1`
   coordinates respectively.
2. **Harmonic-mean edge bound** (`sum_harmonic_update_le_two_mul_sum`): since
   `2 a b / (a + b) ≤ 2 min a b` for `a, b ≥ 0`, the harmonic-mean edge sum is at most
   `2 d · ∑ f, μ f`, obtained directly from the weighted shifting step without an edge-orientation
   argument.
3. **Random-projection fiber gap** (`mul_sub_expect_card_image_le`): applying the harmonic-mean
   bound to fiber multiplicities of `P` on uniform `(r + 1)`-tuples `t : Fin (r + 1) → Fin m`
   (sampled *with replacement*, so the argument allows `r = ⌊2 (d + 1) / ε⌋₊` even when `r ≥ m`)
   and counting within-fiber disagreements across the `(r + 1)`-st coordinate yields
   `((r + 1) ε - 2 d) |P| ≤ (r + 1) ε · 𝔼_s [|P|_s|]`.
4. **Haussler's Boolean `n`-cube sphere-packing theorem**
   (`card_le_exp_mul_add_one_mul_pow_of_setShatters`, `card_le_exp_mul_add_one_mul_pow`,
   [Haussler1995]): choosing `r = ⌊2 (d + 1) / ε⌋₊` and bounding `|P|_s|` by
   `growthFunction_le_exp_mul_pow` at `T = 2 / ε` gives `|P| ≤ e (d + 1) (2 e / ε) ^ d` for
   `0 < ε ≤ 1`, along with the `vcDim` form and the maximal-packing covering-net bound
   (`exists_covering_haussler`). The 1995 *J. Combin. Theory Ser. A* PDF has not been inspected
   firsthand here, so internal lemma/theorem numbers are omitted; the general `L¹(P)` probability-
   measure extension remains open under #4920.

## Main definitions

- `hypercubeEdgeMinSum μ`: sum of `min (μ f) (μ (Function.update f i true))` over hypercube edges
  `(i, f)` with `f i = false`.

## Main results

- `sum_min_update_le_mul_sum`: `hypercubeEdgeMinSum μ ≤ d * ∑ f, μ f` when `{f | 0 < μ f}` shatters
  no finite set of size exceeding `d`.
- `sum_harmonic_update_le_two_mul_sum`: harmonic-mean hypercube edge inequality.
- `mul_sub_expect_card_image_le`: `((r + 1) ε - 2 d) |P| ≤ (r + 1) ε · 𝔼_s [|P|_s|]`.
- `card_le_exp_mul_add_one_mul_pow_of_setShatters`, `card_le_exp_mul_add_one_mul_pow`,
  `card_le_exp_mul_vcDim_add_one_mul_pow`: Haussler's `e (d + 1) (2 e / ε) ^ d` packing bound.
- `exists_covering_haussler`: `ε m`-Hamming covering net of size at most `e (d + 1) (2 e / ε) ^ d`.

## References

* [D. Haussler, *Sphere Packing Numbers for Subsets of the Boolean `n`-Cube with Bounded
  Vapnik-Chervonenkis Dimension*][Haussler1995]
* [R. Vershynin, *High-Dimensional Probability*][Vershynin2018], Section 8.3
-/

public section

open Finset

namespace Cslib.MachineLearning.PACLearning

variable {α ι : Type*}

/-! ### 1. Weighted hypercube min-edge shifting inequality -/

/-- Sum of `min (μ f) (μ (Function.update f i true))` across all undirected hypercube edges `(i, f)`
with `f i = false` (weighted analogue of the hypercube edge count in [Haussler1995]). -/
noncomputable def hypercubeEdgeMinSum [DecidableEq ι] [Fintype ι] (μ : (ι → Bool) → ℝ) : ℝ :=
  ∑ i : ι, ∑ f : ι → Bool,
    if f i = false then min (μ f) (μ (Function.update f i true)) else 0

/-- The edge-minimum sum counts each edge at its endpoint with coordinate `i` equal to `false`. -/
theorem hypercubeEdgeMinSum_eq_sum [DecidableEq ι] [Fintype ι] (μ : (ι → Bool) → ℝ) :
    hypercubeEdgeMinSum μ = ∑ i : ι, ∑ f : ι → Bool,
      if f i = false then min (μ f) (μ (Function.update f i true)) else 0 := by
  rw [hypercubeEdgeMinSum]

private theorem min_add_min_le_min_max_add_min_min (a₀ a₁ b₀ b₁ : ℝ) :
    min a₀ b₀ + min a₁ b₁ ≤ min (max a₀ a₁) (max b₀ b₁) + min (min a₀ a₁) (min b₀ b₁) := by
  rcases le_total a₀ a₁ with ha | ha <;> rcases le_total b₀ b₁ with hb | hb
  · simp only [max_eq_right ha, min_eq_left ha, max_eq_right hb, min_eq_left hb]
    linarith
  · simp only [max_eq_right ha, min_eq_left ha, max_eq_left hb, min_eq_right hb]
    rcases le_total a₀ b₀ with h1 | h1 <;> rcases le_total a₁ b₁ with h2 | h2 <;>
      rcases le_total a₁ b₀ with h3 | h3 <;> rcases le_total a₀ b₁ with h4 | h4 <;>
      simp only [min_eq_left, min_eq_right, *] <;> linarith
  · simp only [max_eq_left ha, min_eq_right ha, max_eq_right hb, min_eq_left hb]
    rcases le_total a₀ b₀ with h1 | h1 <;> rcases le_total a₁ b₁ with h2 | h2 <;>
      rcases le_total b₁ a₀ with h3 | h3 <;> rcases le_total b₀ a₁ with h4 | h4 <;>
      simp only [min_eq_left, min_eq_right, *] <;> linarith
  · simp only [max_eq_left ha, min_eq_right ha, max_eq_left hb, min_eq_right hb]
    linarith

private theorem sum_fin_succ_bool {n : ℕ} (Φ : (Fin (n + 1) → Bool) → ℝ) :
    (∑ f : Fin (n + 1) → Bool, Φ f) =
      ∑ g : Fin n → Bool, (Φ (Fin.cons false g) + Φ (Fin.cons true g)) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp, Fintype.sum_prod_type,
    Fintype.sum_bool]
  simp only [Fin.consEquiv_apply, sum_add_distrib]
  exact add_comm _ _

private theorem setShatters_cons_both {n : ℕ} {S : Set (Fin (n + 1) → Bool)} {W : Set (Fin n)}
    (hW : SetShatters {g | Fin.cons false g ∈ S ∧ Fin.cons true g ∈ S} W) :
    SetShatters S (insert 0 (Fin.succ '' W)) := by
  classical
  intro T hT
  obtain ⟨g, ⟨hg0, hg1⟩, hgT⟩ := hW (W ∩ Fin.succ ⁻¹' T) Set.inter_subset_left
  let b : Bool := decide ((0 : Fin (n + 1)) ∈ T)
  refine ⟨Fin.cons b g, by cases hb : b <;> [exact hg0; exact hg1], Set.ext fun x => ?_⟩
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
  rcases Fin.eq_zero_or_eq_succ x with rfl | ⟨i, rfl⟩
  · simp [b]
  · constructor
    · rintro ⟨hgi, hxins⟩
      simp only [Fin.cons_succ] at hgi
      have hiW : i ∈ W := by
        rcases hxins with h0 | ⟨j, hj, hji⟩
        · exact absurd h0 (Fin.succ_ne_zero i)
        · rwa [Fin.succ_inj.mp hji] at hj
      have hmem : i ∈ g ⁻¹' {true} ∩ W := ⟨hgi, hiW⟩
      rw [hgT] at hmem
      exact hmem.2
    · intro hiT
      have hiW : i ∈ W := by
        rcases hT hiT with h0 | ⟨j, hj, hji⟩
        · exact absurd h0 (Fin.succ_ne_zero i)
        · rwa [Fin.succ_inj.mp hji] at hj
      have hmem : i ∈ g ⁻¹' {true} ∩ W := hgT ▸ ⟨hiW, hiT⟩
      exact ⟨by simpa only [Fin.cons_succ, Set.mem_preimage, Set.mem_singleton_iff] using hmem.1,
        Or.inr ⟨i, hiW, rfl⟩⟩

private theorem sum_min_update_fin_le :
    ∀ {n d : ℕ} {μ : (Fin n → Bool) → ℝ},
      (∀ f, 0 ≤ μ f) →
      (∀ W : Finset (Fin n), SetShatters {f : Fin n → Bool | 0 < μ f} ↑W → W.card ≤ d) →
      hypercubeEdgeMinSum μ ≤ d * ∑ f : Fin n → Bool, μ f
  | 0, d, μ, hμ, _ => by
    have h0 : hypercubeEdgeMinSum μ = 0 := by simp [hypercubeEdgeMinSum]
    rw [h0]
    exact mul_nonneg (Nat.cast_nonneg d) (sum_nonneg fun f _ => hμ f)
  | n + 1, d, μ, hμ, hsh => by
    let μ_max : (Fin n → Bool) → ℝ := fun g => max (μ (Fin.cons false g)) (μ (Fin.cons true g))
    let μ_min : (Fin n → Bool) → ℝ := fun g => min (μ (Fin.cons false g)) (μ (Fin.cons true g))
    have hmax_nonneg : ∀ g, 0 ≤ μ_max g := fun g => le_max_of_le_left (hμ _)
    have hmin_nonneg : ∀ g, 0 ≤ μ_min g := fun g => le_min (hμ _) (hμ _)
    have hsum_total : (∑ f : Fin (n + 1) → Bool, μ f) =
        (∑ g : Fin n → Bool, μ_max g) + ∑ g : Fin n → Bool, μ_min g := by
      rw [sum_fin_succ_bool, ← sum_add_distrib]
      exact sum_congr rfl fun g _ => (max_add_min _ _).symm
    have hedge0 : (∑ f : Fin (n + 1) → Bool,
        if f 0 = false then min (μ f) (μ (Function.update f 0 true)) else 0) =
        ∑ g : Fin n → Bool, μ_min g := by
      rw [sum_fin_succ_bool]
      refine sum_congr rfl fun g _ => ?_
      simp only [Fin.cons_zero, Fin.update_cons_zero, ↓reduceIte, Bool.true_eq_false, add_zero,
        μ_min]
    have hedges_succ : (∑ j : Fin n, ∑ f : Fin (n + 1) → Bool,
        if f j.succ = false then min (μ f) (μ (Function.update f j.succ true)) else 0) ≤
        hypercubeEdgeMinSum μ_max + hypercubeEdgeMinSum μ_min := by
      unfold hypercubeEdgeMinSum
      rw [← sum_add_distrib]
      refine sum_le_sum fun j _ => ?_
      rw [sum_fin_succ_bool, ← sum_add_distrib]
      refine sum_le_sum fun g _ => ?_
      simp only [Fin.cons_succ, ← Fin.cons_update]
      by_cases hgj : g j = false
      · simp only [hgj, ↓reduceIte, μ_max, μ_min]
        exact min_add_min_le_min_max_add_min_min _ _ _ _
      · simp [hgj]
    have hsplit : hypercubeEdgeMinSum μ =
        (∑ f : Fin (n + 1) → Bool,
          if f 0 = false then min (μ f) (μ (Function.update f 0 true)) else 0) +
        ∑ j : Fin n, ∑ f : Fin (n + 1) → Bool,
          if f j.succ = false then min (μ f) (μ (Function.update f j.succ true)) else 0 := by
      unfold hypercubeEdgeMinSum
      exact Fin.sum_univ_succ _
    have hsh_max : ∀ W : Finset (Fin n),
        SetShatters {g : Fin n → Bool | 0 < μ_max g} ↑W → W.card ≤ d := by
      intro W hW
      have hsub : {g : Fin n → Bool | 0 < μ_max g} ⊆
          Fin.tail '' {f : Fin (n + 1) → Bool | 0 < μ f} := by
        intro g hg
        rcases lt_max_iff.mp (show 0 < μ_max g from hg) with hg0 | hg1
        · exact ⟨Fin.cons false g, hg0, by simp [Fin.tail_cons]⟩
        · exact ⟨Fin.cons true g, hg1, by simp [Fin.tail_cons]⟩
      have hsh' : SetShatters {f : Fin (n + 1) → Bool | 0 < μ f} ↑(W.map (Fin.succEmb n)) := by
        rw [coe_map]
        exact SetShatters.image_of_comp (hW.superset hsub)
      simpa only [card_map] using hsh _ hsh'
    have hsh_min : ∀ W : Finset (Fin n),
        SetShatters {g : Fin n → Bool | 0 < μ_min g} ↑W → W.card + 1 ≤ d := by
      intro W hW
      have hsub : {g : Fin n → Bool | 0 < μ_min g} ⊆
          {g | Fin.cons false g ∈ {f : Fin (n + 1) → Bool | 0 < μ f} ∧
            Fin.cons true g ∈ {f : Fin (n + 1) → Bool | 0 < μ f}} :=
        fun g hg => lt_min_iff.mp (show 0 < μ_min g from hg)
      have h0not : (0 : Fin (n + 1)) ∉ W.map (Fin.succEmb n) := by
        simp only [mem_map, Fin.coe_succEmb, not_exists, not_and]
        exact fun i _ => Fin.succ_ne_zero i
      have hsh' : SetShatters {f : Fin (n + 1) → Bool | 0 < μ f}
          ↑(insert 0 (W.map (Fin.succEmb n))) := by
        rw [coe_insert, coe_map]
        exact setShatters_cons_both (hW.superset hsub)
      have hcard := hsh _ hsh'
      rwa [card_insert_of_notMem h0not, card_map] at hcard
    rcases d with _ | d
    · have hmin_zero : ∀ g : Fin n → Bool, μ_min g = 0 := by
        intro g
        by_contra hne
        have hpos : 0 < μ_min g := lt_of_le_of_ne (hmin_nonneg g) (Ne.symm hne)
        have hsh0 : SetShatters {g' : Fin n → Bool | 0 < μ_min g'} ↑(∅ : Finset (Fin n)) := by
          intro T hT
          have hTeq : T = ∅ := Set.subset_empty_iff.mp (by simpa using hT)
          subst hTeq
          exact ⟨g, hpos, by simp⟩
        have := hsh_min ∅ hsh0
        omega
      have ih_max := sum_min_update_fin_le (d := 0) hmax_nonneg hsh_max
      have he_min : hypercubeEdgeMinSum μ_min = 0 := by
        simp [hypercubeEdgeMinSum, hmin_zero]
      have hs_min : (∑ g : Fin n → Bool, μ_min g) = 0 := by simp [hmin_zero]
      push_cast at ih_max ⊢
      linarith [hsplit, hedge0, hedges_succ]
    · have ih_max := sum_min_update_fin_le (d := d + 1) hmax_nonneg hsh_max
      have ih_min := sum_min_update_fin_le (d := d) hmin_nonneg fun W hW => by
        have := hsh_min W hW; omega
      push_cast at ih_max ⊢
      nlinarith [hsplit, hedge0, hedges_succ, hsum_total]

/-- **Weighted hypercube edge-density inequality** (a weighted coordinate-shifting strengthening of
the edge-density lemma in [Haussler1995]): if `μ : (ι → Bool) → ℝ` is nonnegative and its support
`{f | 0 < μ f}` shatters no finite set of more than `d` coordinates, then
`hypercubeEdgeMinSum μ ≤ d * ∑ f, μ f`. -/
theorem sum_min_update_le_mul_sum [DecidableEq ι] [Fintype ι] {d : ℕ} {μ : (ι → Bool) → ℝ}
    (hμ : ∀ f, 0 ≤ μ f)
    (hsh : ∀ W : Finset ι, SetShatters {f : ι → Bool | 0 < μ f} ↑W → W.card ≤ d) :
    hypercubeEdgeMinSum μ ≤ d * ∑ f : ι → Bool, μ f := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let ef : (Fin (Fintype.card ι) → Bool) ≃ (ι → Bool) := Equiv.arrowCongr e (Equiv.refl Bool)
  let μ' : (Fin (Fintype.card ι) → Bool) → ℝ := fun g => μ (ef g)
  have hsum_eq : (∑ g : Fin (Fintype.card ι) → Bool, μ' g) = ∑ f : ι → Bool, μ f :=
    ef.sum_comp μ
  have hedge_eq : hypercubeEdgeMinSum μ' = hypercubeEdgeMinSum μ := by
    unfold hypercubeEdgeMinSum
    rw [← e.sum_comp]
    refine sum_congr rfl fun j _ => ?_
    rw [← ef.sum_comp]
    refine sum_congr rfl fun g _ => ?_
    have hgj : (ef g) (e j) = g j := by simp [ef, Equiv.arrowCongr]
    have hupd : ef (Function.update g j true) = Function.update (ef g) (e j) true := by
      ext x
      by_cases hx : x = e j
      · subst hx; simp [ef, Equiv.arrowCongr]
      · have hxj : e.symm x ≠ j := fun h => hx (by rw [← h, Equiv.apply_symm_apply])
        simp [ef, Equiv.arrowCongr, hx, hxj]
    simp only [hgj, μ', hupd]
  have hsh' : ∀ W : Finset (Fin (Fintype.card ι)),
      SetShatters {g : Fin (Fintype.card ι) → Bool | 0 < μ' g} ↑W → W.card ≤ d := by
    intro W hW
    have hsub : {g : Fin (Fintype.card ι) → Bool | 0 < μ' g} ⊆
        (fun f : ι → Bool => f ∘ e) '' {f : ι → Bool | 0 < μ f} := by
      intro g hg
      refine ⟨ef g, hg, ?_⟩
      ext j
      simp [ef, Equiv.arrowCongr]
    exact (hW.superset hsub).card_le_of_comp hsh
  rw [← hedge_eq, ← hsum_eq]
  exact sum_min_update_fin_le (fun g => hμ (ef g)) hsh'

/-- Harmonic-mean hypercube edge inequality: under the hypotheses of `sum_min_update_le_mul_sum`,
`∑ i, ∑ f, (if f i = false then 2 μ(f) μ(f⊕e_i) / (μ(f) + μ(f⊕e_i)) else 0) ≤ 2 d ∑ f, μ(f)`. -/
theorem sum_harmonic_update_le_two_mul_sum [DecidableEq ι] [Fintype ι] {d : ℕ}
    {μ : (ι → Bool) → ℝ} (hμ : ∀ f, 0 ≤ μ f)
    (hsh : ∀ W : Finset ι, SetShatters {f : ι → Bool | 0 < μ f} ↑W → W.card ≤ d) :
    (∑ i : ι, ∑ f : ι → Bool,
      if f i = false then
        2 * μ f * μ (Function.update f i true) / (μ f + μ (Function.update f i true))
      else 0) ≤ 2 * d * ∑ f : ι → Bool, μ f := by
  have hle : (∑ i : ι, ∑ f : ι → Bool,
      if f i = false then
        2 * μ f * μ (Function.update f i true) / (μ f + μ (Function.update f i true))
      else 0) ≤ 2 * hypercubeEdgeMinSum μ := by
    unfold hypercubeEdgeMinSum
    rw [mul_sum]
    refine sum_le_sum fun i _ => ?_
    rw [mul_sum]
    refine sum_le_sum fun f _ => ?_
    by_cases hfi : f i = false
    · simp only [hfi, ↓reduceIte]
      set a := μ f
      set b := μ (Function.update f i true)
      have ha : 0 ≤ a := hμ f
      have hb : 0 ≤ b := hμ (Function.update f i true)
      rcases eq_or_lt_of_le (add_nonneg ha hb) with hab0 | hab_pos
      · have ha0 : a = 0 := by linarith
        rw [ha0]
        simp [hb]
      · rw [div_le_iff₀ hab_pos]
        rcases le_total a b with hab | hba
        · rw [min_eq_left hab]
          nlinarith
        · rw [min_eq_right hba]
          nlinarith
    · simp [hfi]
  have hmin := sum_min_update_le_mul_sum hμ hsh
  linarith

/-! ### 2. Random-projection fiber gap and Haussler's sphere-packing bound -/

private def fiberCount {m n : ℕ} (P : Finset (Fin m → Bool)) (t : Fin n → Fin m)
    (f : Fin n → Bool) : ℝ :=
  ((P.filter fun u => u ∘ t = f).card : ℝ)

private noncomputable def coordHarmonic {m n : ℕ} (P : Finset (Fin m → Bool)) (t : Fin n → Fin m)
    (i : Fin n) : ℝ :=
  ∑ f : Fin n → Bool,
    if f i = false then
      2 * fiberCount P t f * fiberCount P t (Function.update f i true) /
        (fiberCount P t f + fiberCount P t (Function.update f i true))
    else 0

private theorem sum_fiberCount_eq_card {m n : ℕ} (P : Finset (Fin m → Bool))
    (t : Fin n → Fin m) :
    (∑ f : Fin n → Bool, fiberCount P t f) = P.card := by
  unfold fiberCount
  rw [← Nat.cast_sum]
  congr 1
  exact (card_eq_sum_card_fiberwise (f := fun u : Fin m → Bool => u ∘ t)
    (t := Finset.univ) fun _ _ => mem_univ _).symm

private theorem sum_coordHarmonic_eq_zero {m r : ℕ} (P : Finset (Fin m → Bool))
    (k : Fin (r + 1)) :
    (∑ t : Fin (r + 1) → Fin m, coordHarmonic P t k) =
      ∑ t : Fin (r + 1) → Fin m, coordHarmonic P t 0 := by
  let σ : Fin (r + 1) ≃ Fin (r + 1) := Equiv.swap 0 k
  let et : (Fin (r + 1) → Fin m) ≃ (Fin (r + 1) → Fin m) :=
    Equiv.arrowCongr σ (Equiv.refl (Fin m))
  let ef : (Fin (r + 1) → Bool) ≃ (Fin (r + 1) → Bool) :=
    Equiv.arrowCongr σ (Equiv.refl Bool)
  rw [← et.sum_comp]
  refine sum_congr rfl fun t _ => ?_
  unfold coordHarmonic
  rw [← ef.sum_comp]
  refine sum_congr rfl fun f _ => ?_
  have hfk : (ef f) k = f 0 := by
    change f (σ.symm k) = f 0
    simp [σ]
  have hfib : ∀ g : Fin (r + 1) → Bool, fiberCount P (et t) (ef g) = fiberCount P t g := by
    intro g
    unfold fiberCount
    congr 2
    ext u
    simp only [mem_filter, and_congr_right_iff]
    intro _
    constructor
    · intro h
      funext j
      have := congrFun h (σ j)
      simpa [et, ef, Equiv.arrowCongr] using this
    · intro h
      funext j
      have := congrFun h (σ.symm j)
      simpa [et, ef, Equiv.arrowCongr] using this
  have hupd : Function.update (ef f) k true = ef (Function.update f 0 true) := by
    ext j
    by_cases hjk : j = k
    · subst hjk
      simp [ef, Equiv.arrowCongr, σ]
    · have h0 : σ.symm j ≠ 0 := by
        intro h
        apply hjk
        have := congrArg σ h
        simpa [σ] using this
      simp [ef, Equiv.arrowCongr, hjk, h0]
  rw [hfk, hupd, hfib f, hfib (Function.update f 0 true)]

private theorem two_mul_card_false_mul_card_true_eq_sum_ne {m : ℕ}
    (Q : Finset (Fin m → Bool)) (i : Fin m) :
    2 * (Q.filter fun u => u i = false).card * (Q.filter fun u => u i = true).card =
      ∑ u ∈ Q, ∑ v ∈ Q, if u i ≠ v i then 1 else 0 := by
  have hinner : ∀ u : Fin m → Bool,
      (∑ v ∈ Q, if u i ≠ v i then 1 else 0) = (Q.filter fun v => v i = !u i).card := by
    intro u
    rw [← card_filter]
    congr 1
    ext v
    cases u i <;> cases v i <;> simp
  simp_rw [hinner]
  rw [← sum_filter_add_sum_filter_not Q (fun u => u i = false)]
  have hnot : (Q.filter fun u => ¬ u i = false) = Q.filter fun u => u i = true := by
    congr 1; ext u; cases u i <;> simp
  have hf : ∀ u ∈ Q.filter (fun u => u i = false),
      (Q.filter fun v => v i = !u i).card = (Q.filter fun v => v i = true).card :=
    fun u hu => by rw [(mem_filter.mp hu).2]; rfl
  have ht : ∀ u ∈ Q.filter (fun u => u i = true),
      (Q.filter fun v => v i = !u i).card = (Q.filter fun v => v i = false).card :=
    fun u hu => by rw [(mem_filter.mp hu).2]; rfl
  rw [hnot, sum_congr rfl hf, sum_congr rfl ht, sum_const, sum_const, smul_eq_mul, smul_eq_mul]
  ring

private theorem sum_coordHarmonic_zero_ge {m r : ℕ} (P : Finset (Fin m → Bool)) {ε : ℝ}
    (hP : ∀ u ∈ P, ∀ v ∈ P, u ≠ v → ε * m ≤ hammingDist u v) (s : Fin r → Fin m) :
    ε * m * ((P.card : ℝ) - (P.image (fun u => u ∘ s)).card) ≤
      ∑ i : Fin m, coordHarmonic P (Fin.cons i s) 0 := by
  classical
  let V := P.image fun u => u ∘ s
  have hcoord : ∀ i : Fin m,
      (∑ w ∈ V,
        2 * fiberCount P (Fin.cons i s) (Fin.cons false w) *
          fiberCount P (Fin.cons i s) (Fin.cons true w) /
          (fiberCount P (Fin.cons i s) (Fin.cons false w) +
            fiberCount P (Fin.cons i s) (Fin.cons true w))) ≤
      coordHarmonic P (Fin.cons i s) 0 := by
    intro i
    unfold coordHarmonic
    rw [sum_fin_succ_bool]
    have hterm : ∀ w : Fin r → Bool,
        (if (Fin.cons false w : Fin (r + 1) → Bool) 0 = false then
          2 * fiberCount P (Fin.cons i s) (Fin.cons false w) *
            fiberCount P (Fin.cons i s) (Function.update (Fin.cons false w) 0 true) /
            (fiberCount P (Fin.cons i s) (Fin.cons false w) +
              fiberCount P (Fin.cons i s) (Function.update (Fin.cons false w) 0 true))
        else 0) +
        (if (Fin.cons true w : Fin (r + 1) → Bool) 0 = false then
          2 * fiberCount P (Fin.cons i s) (Fin.cons true w) *
            fiberCount P (Fin.cons i s) (Function.update (Fin.cons true w) 0 true) /
            (fiberCount P (Fin.cons i s) (Fin.cons true w) +
              fiberCount P (Fin.cons i s) (Function.update (Fin.cons true w) 0 true))
        else 0) =
        2 * fiberCount P (Fin.cons i s) (Fin.cons false w) *
          fiberCount P (Fin.cons i s) (Fin.cons true w) /
          (fiberCount P (Fin.cons i s) (Fin.cons false w) +
            fiberCount P (Fin.cons i s) (Fin.cons true w)) := by
      intro w
      simp only [Fin.cons_zero, Fin.update_cons_zero, ↓reduceIte, Bool.true_eq_false, add_zero]
    simp_rw [hterm]
    refine sum_le_univ_sum_of_nonneg fun w => ?_
    unfold fiberCount
    positivity
  have hsum_le : (∑ i : Fin m, ∑ w ∈ V,
      2 * fiberCount P (Fin.cons i s) (Fin.cons false w) *
        fiberCount P (Fin.cons i s) (Fin.cons true w) /
        (fiberCount P (Fin.cons i s) (Fin.cons false w) +
          fiberCount P (Fin.cons i s) (Fin.cons true w))) ≤
      ∑ i : Fin m, coordHarmonic P (Fin.cons i s) 0 :=
    sum_le_sum fun i _ => hcoord i
  refine le_trans ?_ hsum_le
  rw [sum_comm]
  have hfib_sum : (∑ w ∈ V, ((P.filter fun u => u ∘ s = w).card : ℝ)) = P.card := by
    rw [← Nat.cast_sum]
    congr 1
    exact (card_eq_sum_card_fiberwise (f := fun u : Fin m → Bool => u ∘ s) (t := V)
      fun u hu => mem_image_of_mem _ hu).symm
  have h_lhs : ε * m * ((P.card : ℝ) - V.card) =
      ∑ w ∈ V, ε * m * (((P.filter fun u => u ∘ s = w).card : ℝ) - 1) := by
    rw [← mul_sum, sum_sub_distrib, hfib_sum, sum_const, nsmul_eq_mul, mul_one]
  rw [h_lhs]
  refine sum_le_sum fun w hw => ?_
  let Q := P.filter fun u => u ∘ s = w
  obtain ⟨u₀, hu₀P, hu₀w⟩ := mem_image.mp hw
  have hQ_pos : 0 < Q.card := card_pos.mpr ⟨u₀, mem_filter.mpr ⟨hu₀P, hu₀w⟩⟩
  have hQ_pos_real : (0 : ℝ) < Q.card := by exact_mod_cast hQ_pos
  have hfib_eq : ∀ (i : Fin m) (b : Bool),
      fiberCount P (Fin.cons i s) (Fin.cons b w) =
        ((Q.filter fun u => u i = b).card : ℝ) := by
    intro i b
    unfold fiberCount
    congr 2
    ext u
    simp only [Q, mem_filter, and_assoc]
    refine and_congr_right fun _ => ?_
    constructor
    · intro h
      refine ⟨funext fun j => ?_, ?_⟩
      · simpa using congrFun h j.succ
      · simpa using congrFun h 0
    · rintro ⟨hus, hui⟩
      ext k
      rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨j, rfl⟩
      · simpa using hui
      · simpa using congrFun hus j
  have hden_eq : ∀ i : Fin m,
      fiberCount P (Fin.cons i s) (Fin.cons false w) +
        fiberCount P (Fin.cons i s) (Fin.cons true w) = (Q.card : ℝ) := by
    intro i
    rw [hfib_eq i false, hfib_eq i true, ← Nat.cast_add]
    congr 1
    have hnot : (Q.filter fun u => ¬ u i = false) = Q.filter fun u => u i = true := by
      congr 1; ext u; cases u i <;> simp
    rw [← hnot]
    exact card_filter_add_card_filter_not _
  simp_rw [hden_eq, hfib_eq _ false, hfib_eq _ true, div_eq_mul_inv, ← sum_mul, ← div_eq_mul_inv]
  rw [le_div_iff₀ hQ_pos_real]
  have hnum_nat : (∑ i : Fin m,
      2 * (Q.filter fun u => u i = false).card * (Q.filter fun u => u i = true).card) =
      ∑ p ∈ Q.offDiag, hammingDist p.1 p.2 := by
    simp_rw [two_mul_card_false_mul_card_true_eq_sum_ne]
    rw [sum_comm]
    calc (∑ u ∈ Q, ∑ i : Fin m, ∑ v ∈ Q, if u i ≠ v i then 1 else 0)
        = ∑ u ∈ Q, ∑ v ∈ Q, ∑ i : Fin m, if u i ≠ v i then 1 else 0 :=
          sum_congr rfl fun u _ => sum_comm
      _ = ∑ u ∈ Q, ∑ v ∈ Q, hammingDist u v := by
          refine sum_congr rfl fun u _ => sum_congr rfl fun v _ => ?_
          rw [hammingDist, card_filter]
      _ = ∑ p ∈ Q ×ˢ Q, hammingDist p.1 p.2 := (sum_product' _ _ _).symm
      _ = ∑ p ∈ Q.offDiag, hammingDist p.1 p.2 := by
          have hsub_off : Q.offDiag ⊆ Q ×ˢ Q := fun p hp =>
            mem_product.mpr ⟨(mem_offDiag.mp hp).1, (mem_offDiag.mp hp).2.1⟩
          refine (sum_subset hsub_off fun p hp hnot => ?_).symm
          rcases mem_product.mp hp with ⟨h1, h2⟩
          have heq : p.1 = p.2 := not_not.mp fun hne => hnot (mem_offDiag.mpr ⟨h1, h2, hne⟩)
          simp [heq]
  have hnum_real : (∑ i : Fin m,
      2 * ((Q.filter fun u => u i = false).card : ℝ) *
        ((Q.filter fun u => u i = true).card : ℝ)) =
      ∑ p ∈ Q.offDiag, (hammingDist p.1 p.2 : ℝ) := by
    exact_mod_cast hnum_nat
  rw [hnum_real]
  calc ε * m * ((Q.card : ℝ) - 1) * Q.card
      = (Q.offDiag.card : ℝ) * (ε * m) := by
          rw [offDiag_card, Nat.cast_sub (Nat.le_mul_self Q.card), Nat.cast_mul]
          ring
    _ = ∑ _ ∈ Q.offDiag, ε * m := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ p ∈ Q.offDiag, (hammingDist p.1 p.2 : ℝ) := by
          refine sum_le_sum fun p hp => ?_
          rcases mem_offDiag.mp hp with ⟨hp1, hp2, hne⟩
          exact hP p.1 (mem_filter.mp hp1).1 p.2 (mem_filter.mp hp2).1 hne

/-- **Random-projection fiber gap** [Haussler1995]: for an `ε`-separated subset `P` of `{0, 1}^m`
(`0 < m`) whose shattered sets have size at most `d`, and any `r : ℕ`,
`((r + 1) ε - 2 d) |P| ≤ (r + 1) ε · (∑ s : Fin r → Fin m, |P|_s|) / m ^ r`. -/
theorem mul_sub_expect_card_image_le {m d : ℕ} (hm : 0 < m) {P : Finset (Fin m → Bool)}
    (hsh : ∀ W : Finset (Fin m), SetShatters (P : Set (Fin m → Bool)) ↑W → W.card ≤ d)
    {ε : ℝ} (hP : ∀ u ∈ P, ∀ v ∈ P, u ≠ v → ε * m ≤ hammingDist u v) (r : ℕ) :
    (((r : ℝ) + 1) * ε - 2 * d) * P.card ≤
      ((r : ℝ) + 1) * ε *
        ((∑ s : Fin r → Fin m, ((P.image (fun u => u ∘ s)).card : ℝ)) / (m : ℝ) ^ r) := by
  have hm_pow : (0 : ℝ) < (m : ℝ) ^ r := by positivity
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm
  -- Upper bound on `∑ t, ∑ k, coordHarmonic P t k` via `sum_harmonic_update_le_two_mul_sum`.
  have hub_t : ∀ t : Fin (r + 1) → Fin m,
      (∑ k : Fin (r + 1), coordHarmonic P t k) ≤ 2 * d * P.card := by
    intro t
    have hsh_t : ∀ W : Finset (Fin (r + 1)),
        SetShatters {f : Fin (r + 1) → Bool | 0 < fiberCount P t f} ↑W → W.card ≤ d := by
      intro W hW
      have hsub : {f : Fin (r + 1) → Bool | 0 < fiberCount P t f} ⊆
          (fun u : Fin m → Bool => u ∘ t) '' (P : Set (Fin m → Bool)) := by
        intro f hf
        have hf' : 0 < ((P.filter fun u => u ∘ t = f).card : ℝ) := hf
        have hpos : 0 < (P.filter fun u => u ∘ t = f).card := Nat.cast_pos.mp hf'
        obtain ⟨u, hu⟩ := card_pos.mp hpos
        exact ⟨u, (mem_filter.mp hu).1, (mem_filter.mp hu).2⟩
      exact (hW.superset hsub).card_le_of_comp hsh
    have hharm := sum_harmonic_update_le_two_mul_sum (fun f => by unfold fiberCount; positivity)
      hsh_t
    rwa [sum_fiberCount_eq_card] at hharm
  have hub_total : (∑ t : Fin (r + 1) → Fin m, ∑ k : Fin (r + 1), coordHarmonic P t k) ≤
      ((m : ℝ) ^ (r + 1)) * (2 * d * P.card) := by
    calc (∑ t : Fin (r + 1) → Fin m, ∑ k : Fin (r + 1), coordHarmonic P t k)
        ≤ ∑ _ : Fin (r + 1) → Fin m, (2 * d * (P.card : ℝ)) := sum_le_sum fun t _ => hub_t t
      _ = ((m : ℝ) ^ (r + 1)) * (2 * d * P.card) := by
          rw [sum_const, nsmul_eq_mul, card_univ, Fintype.card_fun, Fintype.card_fin,
            Fintype.card_fin, Nat.cast_pow]
  -- Lower bound via symmetry across `k : Fin (r + 1)` and `sum_coordHarmonic_zero_ge`.
  have hsym : (∑ t : Fin (r + 1) → Fin m, ∑ k : Fin (r + 1), coordHarmonic P t k) =
      ((r : ℝ) + 1) * ∑ s : Fin r → Fin m, ∑ i : Fin m, coordHarmonic P (Fin.cons i s) 0 := by
    rw [sum_comm]
    simp_rw [sum_coordHarmonic_eq_zero]
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    congr 1
    rw [← (Fin.consEquiv (fun _ : Fin (r + 1) => Fin m)).sum_comp, Fintype.sum_prod_type,
      sum_comm]
    rfl
  have hlb_s : (∑ s : Fin r → Fin m, ε * m * ((P.card : ℝ) - (P.image (fun u => u ∘ s)).card)) ≤
      ∑ s : Fin r → Fin m, ∑ i : Fin m, coordHarmonic P (Fin.cons i s) 0 :=
    sum_le_sum fun s _ => sum_coordHarmonic_zero_ge P hP s
  have hlb_eval : (∑ s : Fin r → Fin m,
      ε * m * ((P.card : ℝ) - (P.image (fun u => u ∘ s)).card)) =
      ε * m * ((m : ℝ) ^ r * P.card -
        ∑ s : Fin r → Fin m, ((P.image (fun u => u ∘ s)).card : ℝ)) := by
    rw [← mul_sum, sum_sub_distrib, sum_const, card_univ, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
  have hcomb : ((r : ℝ) + 1) * (ε * m *
      ((m : ℝ) ^ r * P.card - ∑ s : Fin r → Fin m, ((P.image (fun u => u ∘ s)).card : ℝ))) ≤
      ((m : ℝ) ^ (r + 1)) * (2 * d * P.card) := by
    have h1 : ((r : ℝ) + 1) *
        (∑ s : Fin r → Fin m, ε * m * ((P.card : ℝ) - (P.image (fun u => u ∘ s)).card)) ≤
        ((r : ℝ) + 1) *
          ∑ s : Fin r → Fin m, ∑ i : Fin m, coordHarmonic P (Fin.cons i s) 0 :=
      mul_le_mul_of_nonneg_left hlb_s (by positivity)
    rw [hlb_eval] at h1
    linarith [hsym, hub_total]
  -- Divide out `m ^ (r + 1) = m * m ^ r > 0`.
  set S_avg := (∑ s : Fin r → Fin m, ((P.image (fun u => u ∘ s)).card : ℝ)) / (m : ℝ) ^ r
  have hS_mul : S_avg * (m : ℝ) ^ r =
      ∑ s : Fin r → Fin m, ((P.image (fun u => u ∘ s)).card : ℝ) :=
    div_mul_cancel₀ _ hm_pow.ne'
  rw [← hS_mul, pow_succ'] at hcomb
  have hfactor : ((r : ℝ) + 1) * (ε * m * ((m : ℝ) ^ r * P.card - S_avg * (m : ℝ) ^ r)) =
      ((m : ℝ) * (m : ℝ) ^ r) * (((r : ℝ) + 1) * ε * (P.card - S_avg)) := by ring
  rw [hfactor] at hcomb
  have hdiv := le_of_mul_le_mul_left hcomb (mul_pos hm_pos hm_pow)
  linarith

/-- **Haussler's Sphere-Packing Theorem** for a Boolean subset [Haussler1995]: if
`P : Finset (Fin m → Bool)` shatters no finite set of more than `d` coordinates and its members
pairwise have Hamming distance at least `ε m` (`0 < ε ≤ 1`), then
`P.card ≤ e (d + 1) (2 e / ε) ^ d`. -/
theorem card_le_exp_mul_add_one_mul_pow_of_setShatters {m d : ℕ} {P : Finset (Fin m → Bool)}
    (hsh : ∀ W : Finset (Fin m), SetShatters (P : Set (Fin m → Bool)) ↑W → W.card ≤ d)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hP : ∀ u ∈ P, ∀ v ∈ P, u ≠ v → ε * m ≤ hammingDist u v) :
    (P.card : ℝ) ≤ Real.exp 1 * (d + 1) * (2 * Real.exp 1 / ε) ^ d := by
  have hone : (1 : ℝ) ≤ Real.exp 1 * (d + 1) * (2 * Real.exp 1 / ε) ^ d := by
    have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp zero_le_one
    have hd1 : (1 : ℝ) ≤ d + 1 := by linarith [Nat.cast_nonneg (α := ℝ) d]
    have hpow : (1 : ℝ) ≤ (2 * Real.exp 1 / ε) ^ d :=
      one_le_pow₀ (by rw [le_div_iff₀ hε]; linarith)
    calc (1 : ℝ) = 1 * 1 * 1 := by norm_num
      _ ≤ Real.exp 1 * (d + 1) * (2 * Real.exp 1 / ε) ^ d :=
        mul_le_mul (mul_le_mul he1 hd1 zero_le_one (by positivity)) hpow zero_le_one (by positivity)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hle1 : P.card ≤ 1 := (card_le_univ P).trans (by simp)
    exact (by exact_mod_cast hle1 : (P.card : ℝ) ≤ 1).trans hone
  set r : ℕ := ⌊2 * ((d : ℝ) + 1) / ε⌋₊
  have hr_gt : 2 * ((d : ℝ) + 1) < ((r : ℝ) + 1) * ε := by
    have hlt : 2 * ((d : ℝ) + 1) / ε < (r : ℝ) + 1 := Nat.lt_floor_add_one _
    exact (div_lt_iff₀ hε).mp hlt
  have hr_le : (r : ℝ) ≤ 2 * ((d : ℝ) + 1) / ε :=
    Nat.floor_le (by positivity)
  set T : ℝ := 2 / ε
  have hT1 : 1 ≤ T := by rw [le_div_iff₀ hε]; linarith
  have hproj_le : ∀ s : Fin r → Fin m,
      ((P.image (fun u => u ∘ s)).card : ℝ) ≤ Real.exp 1 * (2 * Real.exp 1 / ε) ^ d := by
    intro s
    have hcard_ncard : (P.image (fun u => u ∘ s)).card =
        (restriction (P : Set (Fin m → Bool)) s).ncard := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext w
      simp only [Finset.mem_coe, Finset.mem_image, mem_restriction]
      exact ⟨fun ⟨u, hu, h⟩ => ⟨u, hu, congrFun h⟩, fun ⟨u, hu, h⟩ => ⟨u, hu, funext h⟩⟩
    have hgf : ((P.image (fun u => u ∘ s)).card : ℝ) ≤ Real.exp (r / T) * T ^ d := by
      have h1 : (P.image (fun u => u ∘ s)).card ≤ growthFunction (P : Set (Fin m → Bool)) r :=
        hcard_ncard.trans_le (ncard_restriction_le_growthFunction _ s)
      exact (by exact_mod_cast h1 : ((P.image (fun u => u ∘ s)).card : ℝ) ≤ _).trans
        (growthFunction_le_exp_mul_pow hsh r hT1)
    have hrT : (r : ℝ) / T ≤ (d : ℝ) + 1 := by
      have hmul := mul_le_mul_of_nonneg_left hr_le hε.le
      rw [mul_div_cancel₀ _ hε.ne'] at hmul
      rw [show (r : ℝ) / T = ε * r / 2 by simp only [T, div_div_eq_mul_div, mul_comm]]
      linarith
    calc ((P.image (fun u => u ∘ s)).card : ℝ)
        ≤ Real.exp (r / T) * T ^ d := hgf
      _ ≤ Real.exp ((d : ℝ) + 1) * T ^ d := by gcongr
      _ = Real.exp 1 * (Real.exp 1 ^ d * T ^ d) := by
          rw [add_comm, Real.exp_add, show (d : ℝ) = (d : ℕ) * (1 : ℝ) by simp, Real.exp_nat_mul]
          ring
      _ = Real.exp 1 * (2 * Real.exp 1 / ε) ^ d := by
          rw [← mul_pow]
          congr 2
          simp only [T]
          ring
  have havg_le : (∑ s : Fin r → Fin m, ((P.image (fun u => u ∘ s)).card : ℝ)) / (m : ℝ) ^ r ≤
      Real.exp 1 * (2 * Real.exp 1 / ε) ^ d := by
    have hm_pow : (0 : ℝ) < (m : ℝ) ^ r := by positivity
    rw [div_le_iff₀ hm_pow]
    calc (∑ s : Fin r → Fin m, ((P.image (fun u => u ∘ s)).card : ℝ))
        ≤ ∑ _ : Fin r → Fin m, Real.exp 1 * (2 * Real.exp 1 / ε) ^ d :=
          sum_le_sum fun s _ => hproj_le s
      _ = Real.exp 1 * (2 * Real.exp 1 / ε) ^ d * (m : ℝ) ^ r := by
          rw [sum_const, nsmul_eq_mul, card_univ, Fintype.card_fun, Fintype.card_fin,
            Fintype.card_fin, Nat.cast_pow, mul_comm]
  have hgap := mul_sub_expect_card_image_le hm hsh hP r
  set x : ℝ := ((r : ℝ) + 1) * ε
  have hx_sub_pos : 0 < x - 2 * d := by linarith
  have hx_ratio : x ≤ ((d : ℝ) + 1) * (x - 2 * d) := by
    have hd_nonneg : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    nlinarith
  have hP_mul : (x - 2 * d) * P.card ≤ x * (Real.exp 1 * (2 * Real.exp 1 / ε) ^ d) :=
    hgap.trans (mul_le_mul_of_nonneg_left havg_le (by positivity))
  have hB_nonneg : 0 ≤ Real.exp 1 * (2 * Real.exp 1 / ε) ^ d := by positivity
  have hfinal : (x - 2 * d) * P.card ≤
      (x - 2 * d) * (Real.exp 1 * (d + 1) * (2 * Real.exp 1 / ε) ^ d) := by
    calc (x - 2 * d) * P.card
        ≤ x * (Real.exp 1 * (2 * Real.exp 1 / ε) ^ d) := hP_mul
      _ ≤ (((d : ℝ) + 1) * (x - 2 * d)) * (Real.exp 1 * (2 * Real.exp 1 / ε) ^ d) :=
          mul_le_mul_of_nonneg_right hx_ratio hB_nonneg
      _ = (x - 2 * d) * (Real.exp 1 * (d + 1) * (2 * Real.exp 1 / ε) ^ d) := by ring
  exact le_of_mul_le_mul_left hfinal hx_sub_pos

/-- **Haussler's Sphere-Packing Theorem** for concept classes on a sample [Haussler1995]: if every
finite set shattered by `C : ConceptClass α Bool` has at most `d` points, then any `ε`-separated set
`P ⊆ restriction C x` of labelings on `m` sample points (`0 < ε ≤ 1`) has at most
`e (d + 1) (2 e / ε) ^ d` elements, sharpening Dudley's `(8 / ε) ^ (2 d)` bound in
`card_le_div_pow_of_le_hammingDist`. -/
theorem card_le_exp_mul_add_one_mul_pow {C : ConceptClass α Bool} {d : ℕ}
    (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d) {m : ℕ} {x : Fin m → α}
    {P : Finset (Fin m → Bool)} (hPC : ∀ u ∈ P, u ∈ restriction C x) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hP : ∀ u ∈ P, ∀ v ∈ P, u ≠ v → ε * m ≤ hammingDist u v) :
    (P.card : ℝ) ≤ Real.exp 1 * (d + 1) * (2 * Real.exp 1 / ε) ^ d := by
  have hsh : ∀ W : Finset (Fin m), SetShatters (P : Set (Fin m → Bool)) ↑W → W.card ≤ d := by
    intro W hW
    have hsub : (P : Set (Fin m → Bool)) ⊆ (fun c : α → Bool => c ∘ x) '' C := by
      intro u hu
      obtain ⟨c, hc, hcu⟩ := mem_restriction.mp (hPC u hu)
      exact ⟨c, hc, funext hcu⟩
    exact (hW.superset hsub).card_le_of_comp hC
  exact card_le_exp_mul_add_one_mul_pow_of_setShatters hsh hε hε1 hP

/-- Haussler's packing bound stated in terms of `vcDim` for a class of finite VC dimension. -/
theorem card_le_exp_mul_vcDim_add_one_mul_pow {C : ConceptClass α Bool} (hC : HasFiniteVCDim C)
    {m : ℕ} {x : Fin m → α} {P : Finset (Fin m → Bool)} (hPC : ∀ u ∈ P, u ∈ restriction C x)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hP : ∀ u ∈ P, ∀ v ∈ P, u ≠ v → ε * m ≤ hammingDist u v) :
    (P.card : ℝ) ≤ Real.exp 1 * (vcDim C + 1) * (2 * Real.exp 1 / ε) ^ vcDim C :=
  card_le_exp_mul_add_one_mul_pow (fun _ hW => hW.card_le_vcDim hC) hPC hε hε1 hP

/-- **Haussler Hamming covering-number bound:** if every finite set shattered by `C` has size at
most `d`, then for any `m` sample points `x` and `0 < ε ≤ 1`, `restriction C x` admits an
`ε m`-Hamming net `N ⊆ restriction C x` of size at most `e (d + 1) (2 e / ε) ^ d`. -/
theorem exists_covering_haussler {C : ConceptClass α Bool} {d : ℕ}
    (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d) {m : ℕ} (x : Fin m → α) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ N : Finset (Fin m → Bool), (∀ u ∈ N, u ∈ restriction C x) ∧
      (N.card : ℝ) ≤ Real.exp 1 * (d + 1) * (2 * Real.exp 1 / ε) ^ d ∧
      ∀ u ∈ restriction C x, ∃ v ∈ N, (hammingDist v u : ℝ) ≤ ε * m := by
  classical
  let V : Finset (Fin m → Bool) := (Set.toFinite (restriction C x)).toFinset
  obtain ⟨N, hNV, hsep, hcov⟩ := exists_subset_separated_and_covering V hε.le
  have hNC : ∀ u ∈ N, u ∈ restriction C x :=
    fun u hu => (Set.Finite.mem_toFinset _).mp (hNV hu)
  exact ⟨N, hNC, card_le_exp_mul_add_one_mul_pow hC hNC hε hε1 hsep,
    fun u hu => hcov u ((Set.Finite.mem_toFinset _).mpr hu)⟩

end Cslib.MachineLearning.PACLearning
