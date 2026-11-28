/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.HockeyStick
public import CslibFrontier.Probability.PMF.Event
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Differential privacy

A mechanism is a map `M : D → PMF R` from datasets to output distributions. It is
`(ε, δ)`-differentially private with respect to an adjacency relation `Adj` on datasets when
`Pr[M x ∈ S] ≤ exp ε · Pr[M y ∈ S] + δ` for every pair of adjacent datasets `x`, `y` and every
event `S ⊆ R` [DworkRoth2014, Definition 2.4]. Events are arbitrary sets of outputs, measured by
`PMF.toOuterMeasure`, so no measurable structure on `R` is needed.

The adjacency relation is a parameter. Dwork and Roth compare databases at `ℓ₁` distance at most
one (adding or removing one record); Ghosh, Roughgarden and Sundararajan compare databases that
coincide in all but one row [GhoshRoughgardenSundararajan2012, §2.1], which is
`Cslib.Privacy.HammingAdjacent` in `CslibFrontier.Privacy.DifferentialPrivacy.Hamming`. Both are
instances. The definition quantifies over ordered pairs, so a symmetric guarantee needs a symmetric
`Adj`.

The pointwise characterization of pure privacy (`DifferentiallyPrivate.iff_apply_le`) is the
likelihood-ratio form used for mechanisms with a countable range
[GhoshRoughgardenSundararajan2012, §2.1]. It follows from the hockey-stick characterization
(`DifferentiallyPrivate.iff_hockeyStick_le`, via `Cslib.Probability.PMF.hockeyStick`): the optimal
`δ` for a fixed factor `exp ε` is the hockey-stick divergence of `M x` from `M y` at `exp ε`.

## Main definitions

* `Cslib.Privacy.DifferentiallyPrivate`: `(ε, δ)`-differential privacy relative to `Adj`.

## Main results

* `Cslib.Privacy.DifferentiallyPrivate.iff_hockeyStick_le`: the hockey-stick characterization.
* `Cslib.Privacy.DifferentiallyPrivate.iff_apply_le`: pure privacy is a pointwise ratio bound.
* `Cslib.Privacy.DifferentiallyPrivate.bind`, `Cslib.Privacy.DifferentiallyPrivate.map`:
  post-processing by an arbitrary randomized or deterministic map [DworkRoth2014, Prop. 2.1].
* `Cslib.Privacy.DifferentiallyPrivate.trans`: privacy along a composite of two adjacency
  relations, the inductive step of group privacy.

## References

* [DworkRoth2014]
* [GhoshRoughgardenSundararajan2012]
-/

open scoped ENNReal

public section

namespace Cslib.Privacy

universe u v w

variable {D : Type u} {R : Type v} {R' : Type w}

/-- A mechanism `M` is `(ε, δ)`-differentially private with respect to the adjacency relation
`Adj` when, for all adjacent datasets `x`, `y` and every event `S`,
`Pr[M x ∈ S] ≤ exp ε · Pr[M y ∈ S] + δ` [DworkRoth2014, Definition 2.4]. -/
@[expose] def DifferentiallyPrivate (Adj : D → D → Prop) (M : D → PMF R) (ε : ℝ) (δ : ℝ≥0∞) :
    Prop :=
  ∀ ⦃x y⦄, Adj x y → ∀ S : Set R,
    (M x).toOuterMeasure S ≤ ENNReal.ofReal (Real.exp ε) * (M y).toOuterMeasure S + δ

namespace DifferentiallyPrivate

variable {Adj : D → D → Prop} {M : D → PMF R} {ε : ℝ} {δ : ℝ≥0∞}

/-- `(ε, δ)`-differential privacy bounds the hockey-stick divergence of adjacent output
distributions at factor `exp ε` by `δ`, and conversely. -/
theorem iff_hockeyStick_le :
    DifferentiallyPrivate Adj M ε δ ↔
      ∀ ⦃x y⦄, Adj x y →
        Probability.PMF.hockeyStick (ENNReal.ofReal (Real.exp ε)) (M x) (M y) ≤ δ :=
  forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ =>
    Probability.PMF.forall_toOuterMeasure_le_iff_hockeyStick_le ENNReal.ofReal_ne_top _ _ δ

/-- Pure `(ε, 0)`-differential privacy is the pointwise likelihood-ratio bound
`M x r ≤ exp ε · M y r` [GhoshRoughgardenSundararajan2012, §2.1]. -/
theorem iff_apply_le :
    DifferentiallyPrivate Adj M ε 0 ↔
      ∀ ⦃x y⦄, Adj x y → ∀ r, M x r ≤ ENNReal.ofReal (Real.exp ε) * M y r := by
  rw [iff_hockeyStick_le]
  refine forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ => ?_
  rw [nonpos_iff_eq_zero, Probability.PMF.hockeyStick_eq_zero_iff]

/-- A pointwise likelihood-ratio bound gives pure differential privacy. -/
theorem of_apply_le (h : ∀ ⦃x y⦄, Adj x y → ∀ r, M x r ≤ ENNReal.ofReal (Real.exp ε) * M y r) :
    DifferentiallyPrivate Adj M ε 0 :=
  iff_apply_le.mpr h

/-- Differential privacy bounds expectations of `[0, 1]`-valued functions:
`E[g (M x)] ≤ exp ε · E[g (M y)] + δ` for adjacent `x`, `y`. -/
theorem tsum_mul_le (h : DifferentiallyPrivate Adj M ε δ) {x y : D} (hxy : Adj x y)
    {g : R → ℝ≥0∞} (hg : ∀ r, g r ≤ 1) :
    ∑' r, M x r * g r ≤ ENNReal.ofReal (Real.exp ε) * ∑' r, M y r * g r + δ :=
  (Probability.PMF.tsum_mul_le_mul_tsum_mul_add_hockeyStick _ _ _ hg).trans
    (by gcongr; exact iff_hockeyStick_le.mp h hxy)

/-- Differential privacy is monotone in both privacy parameters. -/
theorem mono {ε' : ℝ} {δ' : ℝ≥0∞} (h : DifferentiallyPrivate Adj M ε δ) (hε : ε ≤ ε')
    (hδ : δ ≤ δ') : DifferentiallyPrivate Adj M ε' δ' := fun _ _ hxy S =>
  (h hxy S).trans (by gcongr)

/-- Differential privacy is antitone in the adjacency relation. -/
theorem mono_adj {Adj' : D → D → Prop} (h : DifferentiallyPrivate Adj M ε δ)
    (hAdj : ∀ ⦃x y⦄, Adj' x y → Adj x y) : DifferentiallyPrivate Adj' M ε δ :=
  fun _ _ hxy => h (hAdj hxy)

/-- Post-processing: applying any randomized map `K` to the output of a differentially private
mechanism preserves its privacy parameters [DworkRoth2014, Proposition 2.1]. -/
theorem bind (h : DifferentiallyPrivate Adj M ε δ) (K : R → PMF R') :
    DifferentiallyPrivate Adj (fun x => (M x).bind K) ε δ :=
  iff_hockeyStick_le.mpr fun _ _ hxy =>
    (Probability.PMF.hockeyStick_bind_le _ _ _ K).trans (iff_hockeyStick_le.mp h hxy)

/-- Deterministic post-processing preserves differential privacy. -/
theorem map (h : DifferentiallyPrivate Adj M ε δ) (f : R → R') :
    DifferentiallyPrivate Adj (fun x => (M x).map f) ε δ :=
  iff_hockeyStick_le.mpr fun _ _ hxy =>
    (Probability.PMF.hockeyStick_map_le _ _ _ f).trans (iff_hockeyStick_le.mp h hxy)

/-- Precomposing a mechanism with a map that sends `Adj'`-adjacent datasets to `Adj`-adjacent
ones preserves differential privacy. -/
theorem comp {D' : Type*} {Adj' : D' → D' → Prop} (h : DifferentiallyPrivate Adj M ε δ)
    (f : D' → D) (hf : ∀ ⦃x y⦄, Adj' x y → Adj (f x) (f y)) :
    DifferentiallyPrivate Adj' (M ∘ f) ε δ := fun _ _ hxy => h (hf hxy)

/-- Privacy along the composite of two adjacency relations: if `M` is `(ε₁, δ₁)`-private for
`Adj₁` and `(ε₂, δ₂)`-private for `Adj₂`, it is `(ε₁ + ε₂, δ₁ + exp ε₁ · δ₂)`-private for
`Relation.Comp Adj₁ Adj₂`. -/
theorem trans {Adj₁ Adj₂ : D → D → Prop} {ε₁ ε₂ : ℝ} {δ₁ δ₂ : ℝ≥0∞}
    (h₁ : DifferentiallyPrivate Adj₁ M ε₁ δ₁) (h₂ : DifferentiallyPrivate Adj₂ M ε₂ δ₂) :
    DifferentiallyPrivate (Relation.Comp Adj₁ Adj₂) M (ε₁ + ε₂)
      (δ₁ + ENNReal.ofReal (Real.exp ε₁) * δ₂) := by
  rw [iff_hockeyStick_le]
  rintro x z ⟨y, hxy, hyz⟩
  rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact (Probability.PMF.hockeyStick_mul_le _ _ (M x) (M y) (M z)).trans
    (add_le_add (iff_hockeyStick_le.mp h₁ hxy)
      (mul_le_mul_of_nonneg_left (iff_hockeyStick_le.mp h₂ hyz) zero_le))

end DifferentiallyPrivate

end Cslib.Privacy
