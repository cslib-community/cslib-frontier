/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.LogSpaceDerandomization.RowCompression.NoiseDecay
public import CslibFrontier.Computability.LogSpaceDerandomization.CorrectionRowRecipe
public import CslibFrontier.Computability.LogSpaceDerandomization.PairwiseIndependentHash.RowFourthMoment

/-!
# Fourth-moment row bounds and zero extension

Two-mask clipped-error splitting, row maxima, Minkowski and mask restriction let compression
clients pass from endpoint moments to row envelopes without an independence assumption.
Zero extension is preserved by conditional walks, telescoping prefixes and compression.
These elementary bounds are shared by the actual normalized-atom moment client.
-/

public section
namespace Cslib.RowCompression
open Finset Cslib Cslib.Probability Matrix
open scoped BigOperators

open Classical in
/-- Clipping is retained on the deterministic mean; no absolute mean-error budget is inferred. -/
lemma min_triangle (w a d : ℝ) : min 1 |w - d| ≤ min 1 |a - d| + |w - a| := by
  rcases le_total 1 |a - d| with h | h
  · exact (min_le_left _ _).trans (by rw [min_eq_left h]; linarith [abs_nonneg (w - a)])
  · exact (min_le_right _ _).trans (by rw [min_eq_right h]; linarith [abs_sub_le w a d])

open Classical in
/-- Relative first-coordinate mean discrepancy and absolute second-coordinate discrepancy
use independent conditioning masks. Noise remains uncentered in the common environment. -/
lemma clipped_two_mean_split (w : Fin 2 → ℝ) (a b d v : ℝ) (hd : 0 ≤ d) :
    clippedError d v w ≤
      min 1 (|a - d| / (1 + d)) + min 1 |b - v| + |w 0 - a| / (1 + d) + |w 1 - b| := by
  have hp : 0 < 1 + d := by linarith
  have hrel : min 1 (|w 0 - d| / (1 + d)) ≤ min 1 (|a - d| / (1 + d)) + |w 0 - a| / (1 + d) := by
    simpa only [← sub_div, abs_div, abs_of_pos hp] using
      min_triangle (w 0 / (1 + d)) (a / (1 + d)) (d / (1 + d))
  have habs := min_triangle (w 1) b v
  exact max_le (by linarith [abs_nonneg (w 1 - b), le_min zero_le_one (abs_nonneg (b - v))])
    (by linarith [div_nonneg (abs_nonneg (w 0 - a)) hp.le,
      le_min zero_le_one (div_nonneg (abs_nonneg (a - d)) hp.le)])

open Classical in
/-- A conditional walk is actually zero off its own endpoint mask. -/
lemma conditionalWalk_zero_off {Ω V E : Type*} [Fintype Ω] [Fintype E]
    (X Y : Ω → V → Prop) [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
    (graph : ∀ x y, RotationMap (RetainedPairSlice X Y x y) E)
    (times : V → V → ℕ) (F : Ω → V → V → ℝ) (σ : Ω) (x y : V)
    (hy : ¬Y σ y) : conditionalWalk X Y graph times F σ x y = 0 := by
  simp only [conditionalWalk, mem_filter, mem_univ, hy, and_false, ↓reduceDIte]

open Classical in
/-- Actual secondChannel zero extension, independent of its normalizer or source slice. -/
lemma secondChannel_zero_off {Γ Ζ V : Type*} [Fintype Γ] [Fintype Ζ]
    (X : Γ → V → Prop) (Y : Ζ → V → Prop)
    [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
    (ζ : ℝ) (prep : Γ × Ζ → Matrix V V ℝ) (σ : Γ × Ζ) (x y : V)
    (hy : ¬Y σ.2 y) : CorrectionRowRecipe.secondChannel X Y ζ prep σ x y = 0 := by
  simp only [CorrectionRowRecipe.secondChannel, hy, ↓reduceIte]

open Classical in
/-- Telescoping schedule with a genuinely zero initial second coordinate. This is an identity
for the raw prefix, before any clipping or compression. -/
lemma uncompressed_second_telescope {ι : Type*}
    (pref : ℕ → ι → ℝ) (first : ℕ → ι → ℝ) (raw : ι → Fin 2 → ℝ)
    (hzero : ∀ y, raw y 1 = 0) (i : ℕ) (y : ι) :
    uncompressedRow (fun j y ν => if ν = 0 then first j y else
      pref (j + 1) y - (if j=0 then 0 else pref j y)) raw (i + 1) y 1 = pref (i + 1) y := by
  induction i with
  | zero => simp [uncompressedRow_succ, hzero]
  | succ i ih =>
    rw [uncompressedRow_succ, ih]
    simp only [Fin.isValue, one_ne_zero, ↓reduceIte, Nat.succ_ne_zero, add_sub_cancel]

open Classical in
/-- Zero-extension survives compression: defaults affect only coordinate zero. -/
lemma iterate_second_zero_off {ι : Type*} (S : Finset ι) (n K : ℕ → ℕ) (ρ : ℕ → ℝ)
    (Δ : ℕ → ι → Fin 2 → ℝ) (raw : ι → Fin 2 → ℝ) (y : ι)
    (hr : raw y 1 = 0) (hΔ : ∀ i, Δ i y 1 = 0) (m : ℕ) :
    (iterate S n K ρ Δ ⟨0, raw⟩ m).row y 1 = 0 := by
  induction m with
  | zero => exact hr
  | succ m ih =>
    rw [iterate_succ]
    let st := iterate S n K ρ Δ ⟨0, raw⟩ m
    have hh := updateEntry_mem_Icc (threshold S (n m) (ρ m) st.defaultValue (st.row + Δ m))
      (newDefault S (n m) (K m) (ρ m) st.defaultValue (st.row + Δ m)) ((st.row + Δ m) y) 1
    simp only [st, Pi.add_apply, ih, hΔ, add_zero, defaultEntry, Fin.isValue, one_ne_zero,
      ↓reduceIte, min_self, max_self, Set.mem_Icc] at hh
    exact le_antisymm hh.2 hh.1

open Classical in
/-- Four scope-correct maxima bound the actual full-rank clipped error. The second
coordinate vanishes off usage; no independence is imposed on the maximizing endpoint. -/
lemma full_rank_four_max {ι : Type*} (Ya Yt : Finset ι) (e b₀ b₁ z₀ z₁ : ι → ℝ)
    (h : ∀ y ∈ Ya, e y ≤
      |b₀ y| + (if y ∈ Yt then |b₁ y| else 0) + |z₀ y| + (if y ∈ Yt then |z₁ y| else 0)) :
    kthLargest 1 Ya e ≤ kthLargest 1 Ya (fun y => |b₀ y|) +
      kthLargest 1 Yt (fun y => |b₁ y|) + kthLargest 1 Ya (fun y => |z₀ y|) +
      kthLargest 1 Yt (fun y => |z₁ y|) := by
  refine kthLargest_le (add_nonneg (add_nonneg (add_nonneg kthLargest_nonneg kthLargest_nonneg)
    kthLargest_nonneg) kthLargest_nonneg) fun y hy => ?_
  have hite (f : ι → ℝ) : (if y ∈ Yt then |f y| else 0) ≤ kthLargest 1 Yt (fun y => |f y|) := by
    split_ifs with ht; exacts [abs_le_kthLargest_one Yt f y ht, kthLargest_nonneg]
  linarith [h y hy, abs_le_kthLargest_one Ya b₀ y hy, abs_le_kthLargest_one Ya z₀ y hy,
    hite b₁, hite z₁]

open Classical in
/-- Two-array Minkowski, without independence. -/
lemma vertex_add_budget {Ω V : Type*} [Fintype Ω] [Fintype V]
    (X : Ω → V → Prop) [∀ σ x, Decidable (X σ x)] {N u a b : ℝ}
    (hNu : 0 ≤ N * u) (ha : 0 ≤ a) (hb : 0 ≤ b) (f g : Ω → V → ℝ)
    (hf : vertexNormPow 4 N u X f ≤ a ^ 4) (hg : vertexNormPow 4 N u X g ≤ b ^ 4) :
    vertexNormPow 4 N u X (fun σ x => f σ x + g σ x) ≤ (a + b) ^ 4 := by
  simpa only [Fin.sum_univ_two, Fin.isValue, ↓reduceIte, one_ne_zero, one_mul] using
    vertexNormPow_sum_le_pow_sum (X := X) (by norm_num : 4 ≠ 0) hNu (univ : Finset (Fin 2))
      (fun i => if i = 0 then f else g) (fun _ => 1) (fun i => if i = 0 then a else b)
      (fun _ _ => zero_le_one) (fun i _ => by fin_cases i <;> simp [ha, hb])
      (fun i _ => by fin_cases i; exacts [by simpa using hf, by simpa using hg])

open Classical in
/-- Monotonicity for nonnegative actual row envelopes in the same source environment. -/
lemma vertex_mono_nonneg {Ω V : Type*} [Fintype Ω] [Fintype V]
    (X : Ω → V → Prop) [∀ σ x, Decidable (X σ x)] {N u : ℝ} (hNu : 0 ≤ N * u)
    (f g : Ω → V → ℝ) (hf : ∀ σ x, 0 ≤ f σ x) (hfg : ∀ σ x, f σ x ≤ g σ x) :
    vertexNormPow 4 N u X f ≤ vertexNormPow 4 N u X g := by
  refine mul_le_mul_of_nonneg_left (expect_le_expect fun σ _ => sum_le_sum fun x _ => ?_)
    (inv_nonneg.mpr hNu)
  rw [abs_of_nonneg (hf σ x), abs_of_nonneg ((hf σ x).trans (hfg σ x))]
  exact pow_le_pow_left₀ (hf σ x) (hfg σ x) 4
open Classical in
lemma row_as_vertex {Ω V : Type*} [Fintype Ω] [Fintype V]
    (X Y : Ω → V → Prop) (N u : ℝ) (f : Ω → V → V → ℝ) :
    rowNormPow 4 N u X Y f = vertexNormPow 4 N u
      (fun σ (z : V × V) => X σ z.1 ∧ Y σ z.2) (fun σ z => f σ z.1 z.2) := by
  simp only [rowNormPow, vertexNormPow, sum_filter, Fintype.sum_prod_type]
  congr 2 with σ : 1
  exact sum_congr rfl fun x _ => by by_cases hx : X σ x <;> simp [hx]

open Classical in
lemma row_add_budget {Ω V : Type*} [Fintype Ω] [Fintype V]
    (X Y : Ω → V → Prop) {N u a b : ℝ} (hNu : 0 ≤ N * u) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (f g : Ω → V → V → ℝ)
    (hf : rowNormPow 4 N u X Y f ≤ a ^ 4) (hg : rowNormPow 4 N u X Y g ≤ b ^ 4) :
    rowNormPow 4 N u X Y (fun σ x y => f σ x y + g σ x y) ≤ (a + b) ^ 4 := by
  rw [row_as_vertex] at hf hg ⊢
  exact vertex_add_budget _ hNu ha hb _ _ hf hg

open Classical in
lemma row_mono_abs {Ω V : Type*} [Fintype Ω] [Fintype V]
    (X Y : Ω → V → Prop) {N u : ℝ} (hNu : 0 ≤ N * u)
    (f g : Ω → V → V → ℝ) (h : ∀ σ x y, X σ x → Y σ y → |f σ x y| ≤ |g σ x y|) :
    rowNormPow 4 N u X Y f ≤ rowNormPow 4 N u X Y g :=
  mul_le_mul_of_nonneg_left (expect_le_expect fun σ _ => sum_le_sum fun x hx =>
    sum_le_sum fun y hy =>
      pow_le_pow_left₀ (abs_nonneg _) (h σ x y (mem_filter.mp hx).2 (mem_filter.mp hy).2) 4)
    (inv_nonneg.mpr hNu)

open Classical in
lemma row_const_mul {Ω V : Type*} [Fintype Ω] [Fintype V]
    (X Y : Ω → V → Prop) (N u w : ℝ) (f : Ω → V → V → ℝ) :
    rowNormPow 4 N u X Y (fun σ x y => w * f σ x y) = |w| ^ 4 * rowNormPow 4 N u X Y f := by
  simp only [rowNormPow, abs_mul, mul_pow, ←mul_sum, ←mul_expect]
  ring

open Classical in
lemma vertex_row_max {Ω V : Type*} [Fintype Ω] [Fintype V]
    (X Y : Ω → V → Prop) {N u : ℝ} (hNu : 0 ≤ N * u) (f : Ω → V → V → ℝ) :
    vertexNormPow 4 N u X (fun σ x => kthLargest 1 {y | Y σ y} (fun y => |f σ x y|)) ≤
      rowNormPow 4 N u X Y f := by
  refine mul_le_mul_of_nonneg_left (expect_le_expect fun σ _ => sum_le_sum fun x _ => ?_)
    (inv_nonneg.mpr hNu)
  dsimp only
  have hmem : kthLargest 1 {y | Y σ y} (fun y => |f σ x y|) ∈
      insert 0 ((({y | Y σ y} : Finset V).filter fun y =>
        1 ≤ #{w ∈ ({y | Y σ y} : Finset V) | |f σ x y| ≤ |f σ x w|}).image fun y => |f σ x y|) :=
    max'_mem _ _
  rcases mem_insert.mp hmem with hz | hmem
  · rw [hz, abs_zero, zero_pow (by decide : 4 ≠ 0)]; positivity
  · obtain ⟨y, hy, heq⟩ := mem_image.mp hmem
    rw [← heq, abs_abs]
    exact single_le_sum (f := fun y => |f σ x y| ^ 4) (fun _ _ => by positivity)
      (mem_filter.mp hy).1

open Classical in
lemma row_mask_subset {Ω V : Type*} [Fintype Ω] [Fintype V]
    (X Ya Yt : Ω → V → Prop) (hsub : ∀ σ y, Yt σ y → Ya σ y)
    (N u : ℝ) (f : Ω → V → V → ℝ) :
    rowNormPow 4 N u X Ya (fun σ x y => if Yt σ y then f σ x y else 0) =
      rowNormPow 4 N u X Yt f := by
  unfold rowNormPow
  congr 2 with σ : 1
  refine sum_congr rfl fun x _ => ?_
  simp only [sum_filter]
  exact sum_congr rfl fun y _ => by
    by_cases ht : Yt σ y
    · simp only [ht, hsub σ y ht, ↓reduceIte]
    · simp only [ht, ↓reduceIte, abs_zero, zero_pow (by decide : 4 ≠ 0), ite_self]

end Cslib.RowCompression
