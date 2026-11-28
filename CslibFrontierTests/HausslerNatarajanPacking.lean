/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.PACLearning.HausslerPacking
import CslibFrontier.MachineLearning.PACLearning.NatarajanPacking
import CslibFrontierTests.RealizablePAC

/-! Checks for Haussler's sphere-packing lemma and multiclass Natarajan packing/covering bounds:

1. **Weighted hypercube min-edge inequality (`sum_min_update_le_mul_sum`):** concrete evaluation on
   the uniform weight of `{0, 1}³`, showing `hypercubeEdgeMinSum = 12` exceeds `1 * 8` (because
   `{0, 1}³` shatters sets of size `3 > 1`) while satisfying `12 ≤ 3 * 8`.
2. **Quantitative sharpening of `CslibFrontierTests/Packing.lean` on `thresholds` (`d = 1`):**
   Haussler's bound `e (d + 1) (2 e / ε) ^ d` reduces the `(1 / 2)`-packing bound on thresholds
   from `256` (Dudley) to `59`, and the `(m / 4)`-Hamming net bound from `1024` to `118`, with a
   matching concrete `3`-element `(1 / 2)`-packing on two sample points.
3. **Multiclass (`k = 3`) Natarajan packing and covering (`coloredThresholds`):**
   the `3`-label step functions `x ↦ if x < θ then b else 0` on `ℕ` form an infinite class of
   Natarajan dimension `1`; on any `m` sample points, every `(1 / 2)`-separated set of realized
   labelings has size at most `48 ^ 2 = 2304` and `(· ∘ x) '' coloredThresholds` admits an
   `(m / 2)`-net of size at most `2304`, with a concrete `3`-element `1`-separated witness. -/

namespace CslibFrontierTests.HausslerNatarajanPacking

open Cslib.MachineLearning.PACLearning
open CslibFrontierTests.RealizablePAC (thresholds card_le_one_of_setShatters_thresholds)

/-! ### 1. Weighted hypercube min-edge check on `{0, 1}³` -/

/-- On `{0, 1}³` (`8` vertices, `12` edges), the constant weight `1` has edge-min sum `12 > 1 * 8`
(reflecting `vcDim = 3 > 1`) and `12 ≤ 3 * 8`. -/
theorem hypercubeEdgeMinSum_const_one_fin_three :
    8 < hypercubeEdgeMinSum (fun _ : Fin 3 → Bool => (1 : ℝ)) ∧
      hypercubeEdgeMinSum (fun _ : Fin 3 → Bool => (1 : ℝ)) ≤
        3 * ∑ _ : Fin 3 → Bool, (1 : ℝ) := by
  have heval : hypercubeEdgeMinSum (fun _ : Fin 3 → Bool => (1 : ℝ)) = 12 := by
    rw [hypercubeEdgeMinSum_eq_sum]
    simp only [min_self, Fin.sum_univ_three]
    have hcoord : ∀ i : Fin 3,
        (∑ f : Fin 3 → Bool, if f i = false then (1 : ℝ) else 0) = 4 := by
      intro i
      have hnat : (Finset.univ.filter fun f : Fin 3 → Bool => f i = false).card = 4 := by
        fin_cases i <;> decide
      rw [← Finset.sum_filter, Finset.sum_const, hnat]
      norm_num
    rw [hcoord 0, hcoord 1, hcoord 2]
    norm_num
  refine ⟨by linarith, ?_⟩
  have hle := sum_min_update_le_mul_sum (d := 3) (μ := fun _ : Fin 3 → Bool => (1 : ℝ))
    (fun _ => zero_le_one) (fun W _ => (W.card_le_univ).trans (by simp))
  exact_mod_cast hle

/-! ### 2. Haussler sphere-packing and net bounds on `thresholds` (`d = 1`) -/

/-- `8 e² < 60`, since `e < 2.7182818286 < 2.73`. -/
private theorem eight_mul_exp_one_sq_lt : 8 * Real.exp 1 ^ 2 < 60 := by
  have he_pos : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  have he_lt : Real.exp 1 < 2.73 := Real.exp_one_lt_d9.trans (by norm_num)
  nlinarith

/-- **Sharpened threshold packing bound:** `(1 / 2)`-separated labelings of `m` points by
`thresholds` number at most `59` for every `m` (sharpening `256` from Dudley's bound in
`CslibFrontierTests/Packing.lean`). -/
theorem card_thresholds_half_packing_le_59 {m : ℕ} (x : Fin m → ℕ)
    (P : Finset (Fin m → Bool)) (hPC : ∀ u ∈ P, u ∈ restriction thresholds x)
    (hP : ∀ u ∈ P, ∀ v ∈ P, u ≠ v → (1 / 2 : ℝ) * m ≤ hammingDist u v) :
    P.card ≤ 59 := by
  have h := card_le_exp_mul_add_one_mul_pow
    (fun _ hW => card_le_one_of_setShatters_thresholds hW) hPC (by norm_num) (by norm_num) hP
  have hlt : (P.card : ℝ) < 60 := by
    calc (P.card : ℝ)
        ≤ Real.exp 1 * ((1 : ℕ) + 1) * (2 * Real.exp 1 / (1 / 2)) ^ 1 := h
      _ = 8 * Real.exp 1 ^ 2 := by push_cast; ring
      _ < 60 := eight_mul_exp_one_sq_lt
  have hnat : P.card < 60 := by exact_mod_cast hlt
  omega

/-- **Sharpened threshold net bound:** at Hamming scale `m / 4`, the labelings of any `m` points by
`thresholds` admit a net of at most `118` realized labelings (sharpening `1024` in
`CslibFrontierTests/Packing.lean`). -/
theorem exists_thresholds_quarter_net_le_118 {m : ℕ} (x : Fin m → ℕ) :
    ∃ N : Finset (Fin m → Bool), (∀ u ∈ N, u ∈ restriction thresholds x) ∧ N.card ≤ 118 ∧
      ∀ u ∈ restriction thresholds x, ∃ v ∈ N, hammingDist v u ≤ m / 4 := by
  obtain ⟨N, hNC, hcard, hcov⟩ := exists_covering_haussler (ε := 1 / 4)
    (fun _ hW => card_le_one_of_setShatters_thresholds hW) x (by norm_num) (by norm_num)
  refine ⟨N, hNC, ?_, fun u hu => ?_⟩
  · have hlt119 : (N.card : ℝ) < 119 := by
      have he_pos : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
      have he_lt : Real.exp 1 < 2.72 := Real.exp_one_lt_d9.trans (by norm_num)
      calc (N.card : ℝ)
          ≤ Real.exp 1 * ((1 : ℕ) + 1) * (2 * Real.exp 1 / (1 / 4)) ^ 1 := hcard
        _ = 16 * Real.exp 1 ^ 2 := by push_cast; ring
        _ < 119 := by nlinarith
    have hnat : N.card < 119 := by exact_mod_cast hlt119
    omega
  · obtain ⟨v, hvN, hvu⟩ := hcov u hu
    refine ⟨v, hvN, (Nat.le_div_iff_mul_le (by norm_num)).mpr ?_⟩
    have hreal : (hammingDist v u : ℝ) * 4 ≤ m := by linarith
    exact_mod_cast hreal

/-- Non-vacuity on `m = 2`: on `![0, 1]`, `thresholds` realizes `3` pairwise `(1 / 2)`-separated
labelings `{![false, false], ![false, true], ![true, true]}`. -/
example :
    let P : Finset (Fin 2 → Bool) := {![false, false], ![false, true], ![true, true]}
    P.card = 3 ∧ (∀ u ∈ P, u ∈ restriction thresholds ![0, 1]) ∧
      ∀ u ∈ P, ∀ v ∈ P, u ≠ v → (1 / 2 : ℝ) * 2 ≤ hammingDist u v := by
  refine ⟨by decide, ?_, ?_⟩
  · intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · exact mem_restriction.mpr ⟨fun z => decide (2 ≤ z), ⟨2, rfl⟩, by decide⟩
    · exact mem_restriction.mpr ⟨fun z => decide (1 ≤ z), ⟨1, rfl⟩, by decide⟩
    · exact mem_restriction.mpr ⟨fun z => decide (0 ≤ z), ⟨0, rfl⟩, by decide⟩
  · intro u hu v hv huv
    have hdist : 1 ≤ hammingDist u v := hammingDist_pos.mpr huv
    have hreal : (1 : ℝ) ≤ hammingDist u v := by exact_mod_cast hdist
    linarith

/-! ### 3. Multiclass (`k = 3`) Natarajan packing and covering on infinite `coloredThresholds` -/

/-- Infinite `3`-label class on `ℕ`: points below `θ` take color `b : Fin 3`, and `0` above. -/
def coloredThresholds : ConceptClass ℕ (Fin 3) :=
  {c | ∃ (θ : ℕ) (b : Fin 3), c = fun x => if x < θ then b else 0}

/-- `coloredThresholds` N-shatters `{0}`, witnessed by colors `1` and `0`. -/
theorem natarajanShatters_coloredThresholds_zero :
    NatarajanShatters coloredThresholds ({0} : Set ℕ) := by
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  refine ⟨fun _ => 1, fun _ => 0, fun _ _ => h10, fun B hB => ?_⟩
  rcases Set.subset_singleton_iff_eq.mp hB with rfl | rfl
  · exact ⟨fun x => if x < 0 then 0 else 0, ⟨0, 0, rfl⟩, fun _ hx => hx.elim, fun _ _ => rfl⟩
  · refine ⟨fun x => if x < 1 then 1 else 0, ⟨1, 1, rfl⟩, ?_, ?_⟩
    · intro x hx
      rw [Set.mem_singleton_iff.mp hx]
      decide
    · intro x hx
      exact absurd hx.1 hx.2

/-- `coloredThresholds` N-shatters no two-element subset of `ℕ`: any concept taking a nonzero label
at `max x y` takes the same label at `min x y`. -/
theorem card_le_one_of_natarajanShatters_coloredThresholds (W : Finset ℕ)
    (hW : NatarajanShatters coloredThresholds ↑W) : W.card ≤ 1 := by
  by_contra hlt
  obtain ⟨x, hxW, y, hyW, hxy⟩ := Finset.one_lt_card.mp (not_le.mp hlt)
  wlog hlt_xy : x < y generalizing x y
  · exact this y hyW x hxW hxy.symm (Nat.lt_of_le_of_ne (not_lt.mp hlt_xy) hxy.symm)
  obtain ⟨f₀, f₁, hne, hreal⟩ := hW
  -- At least one of `f₀ y, f₁ y` is nonzero in `Fin 3`.
  have hnz : f₀ y ≠ 0 ∨ f₁ y ≠ 0 := by
    by_contra hall
    rw [not_or, Decidable.not_not, Decidable.not_not] at hall
    exact hne y hyW (hall.1.trans hall.2.symm)
  rcases hnz with hy0 | hy1
  · obtain ⟨_, ⟨θ₁, b₁, rfl⟩, hB0, hB1⟩ := hreal {y} (Set.singleton_subset_iff.mpr hyW)
    obtain ⟨_, ⟨θ₂, b₂, rfl⟩, hA0, _⟩ :=
      hreal {x, y} (by intro z hz; rcases hz with rfl | rfl <;> assumption)
    have hcy₁ : (if y < θ₁ then b₁ else 0) = f₀ y := hB0 y rfl
    have hyθ₁ : y < θ₁ := by
      by_contra h; simp only [h, ↓reduceIte] at hcy₁; exact hy0 hcy₁.symm
    have hcx₁ : b₁ = f₁ x := by
      have := hB1 x ⟨hxW, fun h => hxy (Set.mem_singleton_iff.mp h)⟩
      simpa [hlt_xy.trans hyθ₁] using this
    have hb₁ : b₁ = f₀ y := by simpa [hyθ₁] using hcy₁
    have hcy₂ : (if y < θ₂ then b₂ else 0) = f₀ y := hA0 y (Or.inr rfl)
    have hyθ₂ : y < θ₂ := by
      by_contra h; simp only [h, ↓reduceIte] at hcy₂; exact hy0 hcy₂.symm
    have hcx₂ : b₂ = f₀ x := by
      have := hA0 x (Or.inl rfl)
      simpa [hlt_xy.trans hyθ₂] using this
    have hb₂ : b₂ = f₀ y := by simpa [hyθ₂] using hcy₂
    exact hne x hxW (hcx₂.symm.trans (hb₂.trans (hb₁.symm.trans hcx₁)))
  · obtain ⟨_, ⟨θ₁, b₁, rfl⟩, _, hB1⟩ := hreal ∅ (Set.empty_subset _)
    obtain ⟨_, ⟨θ₂, b₂, rfl⟩, hA0, hA1⟩ := hreal {x} (Set.singleton_subset_iff.mpr hxW)
    have hcy₁ : (if y < θ₁ then b₁ else 0) = f₁ y := hB1 y ⟨hyW, Set.notMem_empty y⟩
    have hyθ₁ : y < θ₁ := by
      by_contra h; simp only [h, ↓reduceIte] at hcy₁; exact hy1 hcy₁.symm
    have hcx₁ : b₁ = f₁ x := by
      have := hB1 x ⟨hxW, Set.notMem_empty x⟩
      simpa [hlt_xy.trans hyθ₁] using this
    have hb₁ : b₁ = f₁ y := by simpa [hyθ₁] using hcy₁
    have hcy₂ : (if y < θ₂ then b₂ else 0) = f₁ y :=
      hA1 y ⟨hyW, fun h => hxy.symm (Set.mem_singleton_iff.mp h)⟩
    have hyθ₂ : y < θ₂ := by
      by_contra h; simp only [h, ↓reduceIte] at hcy₂; exact hy1 hcy₂.symm
    have hcx₂ : b₂ = f₀ x := by
      have := hA0 x rfl
      simpa [hlt_xy.trans hyθ₂] using this
    have hb₂ : b₂ = f₁ y := by simpa [hyθ₂] using hcy₂
    exact hne x hxW (hcx₂.symm.trans (hb₂.trans (hb₁.symm.trans hcx₁)))

theorem natarajanDim_coloredThresholds : natarajanDim coloredThresholds = 1 := by
  refine le_antisymm
    (natarajanDim_le_iff.mpr fun W hW =>
      Nat.cast_le.mpr (card_le_one_of_natarajanShatters_coloredThresholds W hW)) ?_
  have h0 : NatarajanShatters coloredThresholds (({0} : Finset ℕ) : Set ℕ) := by
    simpa using natarajanShatters_coloredThresholds_zero
  simpa using h0.card_le_natarajanDim

/-- On any `m` sample points, `(1 / 2)`-separated labelings realized by the infinite `3`-label
class `coloredThresholds` have size at most `48 ^ 2 = 2304`, and `(· ∘ x) '' coloredThresholds`
admits an `(m / 2)`-Hamming net of size at most `2304`. -/
theorem coloredThresholds_half_packing_and_net {m : ℕ} (x : Fin m → ℕ) :
    (∀ P : Finset (Fin m → Fin 3), (∀ u ∈ P, u ∈ (· ∘ x) '' coloredThresholds) →
      (∀ u ∈ P, ∀ v ∈ P, u ≠ v → (1 / 2 : ℝ) * m ≤ hammingDist u v) → P.card ≤ 2304) ∧
    ∃ N : Finset (Fin m → Fin 3), (∀ u ∈ N, u ∈ (· ∘ x) '' coloredThresholds) ∧ N.card ≤ 2304 ∧
      ∀ u ∈ (· ∘ x) '' coloredThresholds, ∃ v ∈ N, hammingDist v u ≤ m / 2 := by
  have hchoose : (Fintype.card (Fin 3)).choose 2 = 3 := by decide
  constructor
  · intro P hPC hP
    have h := card_le_div_pow_of_natarajanShatters_of_two_le (by decide)
      card_le_one_of_natarajanShatters_coloredThresholds hPC (by norm_num) (by norm_num) hP
    rw [hchoose] at h
    norm_num at h
    exact_mod_cast h
  · obtain ⟨N, hNC, hcard, hcov⟩ := exists_covering_of_natarajanShatters (ε := 1 / 2)
      card_le_one_of_natarajanShatters_coloredThresholds x (by norm_num) (by norm_num)
    refine ⟨N, hNC, ?_, fun u hu => ?_⟩
    · rw [hchoose] at hcard
      norm_num at hcard
      exact_mod_cast hcard
    · obtain ⟨v, hvN, hvu⟩ := hcov u hu
      refine ⟨v, hvN, (Nat.le_div_iff_mul_le (by norm_num)).mpr ?_⟩
      have hreal : (hammingDist v u : ℝ) * 2 ≤ m := by linarith
      exact_mod_cast hreal

/-- Non-vacuity on `m = 2`: `coloredThresholds` realizes `3` pairwise maximally-separated
labelings `{![0, 0], ![1, 1], ![2, 2]}` at Hamming distance `2` on `![0, 1]`. -/
example :
    let P : Finset (Fin 2 → Fin 3) := {![0, 0], ![1, 1], ![2, 2]}
    P.card = 3 ∧ (∀ u ∈ P, u ∈ (· ∘ ![0, 1]) '' coloredThresholds) ∧
      ∀ u ∈ P, ∀ v ∈ P, u ≠ v → hammingDist u v = 2 := by
  refine ⟨by decide, ?_, by decide⟩
  intro u hu
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with rfl | rfl | rfl
  · exact ⟨fun x => if x < 0 then 0 else 0, ⟨0, 0, rfl⟩, by decide⟩
  · exact ⟨fun x => if x < 2 then 1 else 0, ⟨2, 1, rfl⟩, by decide⟩
  · exact ⟨fun x => if x < 2 then 2 else 0, ⟨2, 2, rfl⟩, by decide⟩

end CslibFrontierTests.HausslerNatarajanPacking
