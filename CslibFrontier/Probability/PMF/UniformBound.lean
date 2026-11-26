/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PMF
public import Mathlib.Data.Finset.Density
import CslibFrontier.Probability.PMF.BindFailure
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Data.List.Dedup
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Natural-Number Sum, Density, and Conditional Bounds for `PMF.uniformOfFintype`

This module converts natural-number sum bounds `(∑ a : α, f a) ≤ C * Fintype.card α`,
filter-cardinality bounds `B * #{a : α | P a} ≤ A * Fintype.card α`, `Finset.dens` real upper
bounds, target-list membership events `{a : α | a ∈ targets}`, and product-equivalence conditional
bounds over nonempty finite types into `ℝ≥0∞` expectation and outer-measure bounds under
`PMF.uniformOfFintype`.

## Main results

* `Cslib.Probability.PMF.tsum_uniformOfFintype_le_of_sum_le`: converts
  `(∑ a : α, f a) ≤ C * Fintype.card α` into
  `(∑' a : α, PMF.uniformOfFintype α a * (f a : ℝ≥0∞)) ≤ (C : ℝ≥0∞)`.
* `Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_le_div`: converts
  `B * (Finset.univ.filter P).card ≤ A * Fintype.card α` into
  `(PMF.uniformOfFintype α).toOuterMeasure {a : α | P a} ≤ (A : ℝ≥0∞) / (B : ℝ≥0∞)`.
* `Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_mem_list_le`: bounds
  `(PMF.uniformOfFintype α).toOuterMeasure {a : α | a ∈ targets}` by
  `(targets.length : ℝ≥0∞) * ((1 : ℝ≥0∞) / Fintype.card α)`.
* `Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_le_of_dens_le`: converts `E ⊆ ↑F` and
  `(F.dens : ℝ) ≤ B` into `(PMF.uniformOfFintype α).toOuterMeasure E ≤ ENNReal.ofReal B`.
* `Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_fst`,
  `Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_cond_le`: marginal identity and conditional
  union bound along `e : γ ≃ α × β`.
-/

public section

namespace Cslib.Probability.PMF

open scoped BigOperators ENNReal

/-- Convert a natural-number sum bound `(∑ a : α, f a) ≤ C * Fintype.card α` over a nonempty finite
type `α` into an `ℝ≥0∞` expectation bound under `PMF.uniformOfFintype α`. -/
theorem tsum_uniformOfFintype_le_of_sum_le {α : Type*} [Fintype α] [Nonempty α]
    {f : α → ℕ} {C : ℕ} (hle : (∑ a : α, f a) ≤ C * Fintype.card α) :
    (∑' a : α, PMF.uniformOfFintype α a * (f a : ℝ≥0∞)) ≤ (C : ℝ≥0∞) := by
  rw [tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, ← Finset.mul_sum, ← Nat.cast_sum]
  calc (Fintype.card α : ℝ≥0∞)⁻¹ * ((∑ a : α, f a : ℕ) : ℝ≥0∞)
      ≤ (Fintype.card α : ℝ≥0∞)⁻¹ * ((C : ℝ≥0∞) * Fintype.card α) := by
        gcongr
        exact_mod_cast hle
    _ = (C : ℝ≥0∞) * ((Fintype.card α : ℝ≥0∞)⁻¹ * Fintype.card α) := by ring
    _ = C := by
      rw [ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
        (ENNReal.natCast_ne_top _), mul_one]

/-- Convert a natural-number filter-cardinality bound
`B * (Finset.univ.filter P).card ≤ A * Fintype.card α` into an `ℝ≥0∞` outer-measure bound
`(PMF.uniformOfFintype α).toOuterMeasure {a : α | P a} ≤ (A : ℝ≥0∞) / (B : ℝ≥0∞)`. -/
theorem toOuterMeasure_uniformOfFintype_le_div {α : Type*} [Fintype α] [Nonempty α]
    {P : α → Prop} [DecidablePred P] {A B : ℕ} (hB : 0 < B)
    (hle : B * (Finset.univ.filter P).card ≤ A * Fintype.card α) :
    (PMF.uniformOfFintype α).toOuterMeasure {a : α | P a} ≤ (A : ℝ≥0∞) / (B : ℝ≥0∞) := by
  have h1 := PMF.toOuterMeasure_uniformOfFintype (α := α) {a : α | P a}
  simp only [Set.mem_ofPred_eq] at h1
  have hcast : (B : ℝ≥0∞) * (Finset.univ.filter P).card ≤ A * Fintype.card α := by
    exact_mod_cast hle
  rw [h1, ENNReal.le_div_iff_mul_le (Or.inl (Nat.cast_ne_zero.mpr hB.ne'))
    (Or.inl (ENNReal.natCast_ne_top _))]
  calc ((Finset.univ.filter P).card : ℝ≥0∞) * (Fintype.card α : ℝ≥0∞)⁻¹ * B
      = ((B : ℝ≥0∞) * (Finset.univ.filter P).card) * (Fintype.card α : ℝ≥0∞)⁻¹ := by ring
    _ ≤ ((A : ℝ≥0∞) * Fintype.card α) * (Fintype.card α : ℝ≥0∞)⁻¹ := by gcongr
    _ = (A : ℝ≥0∞) * (Fintype.card α * (Fintype.card α : ℝ≥0∞)⁻¹) := by ring
    _ = A := by
      rw [ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
        (ENNReal.natCast_ne_top _), mul_one]

/-- **Target-hitting union bound for `PMF.uniformOfFintype`**: a uniformly sampled `a : α` lands in
`targets` with probability at most `targets.length * (1 / Fintype.card α)`. -/
theorem toOuterMeasure_uniformOfFintype_mem_list_le {α : Type*} [Fintype α] [Nonempty α]
    (targets : List α) :
    (PMF.uniformOfFintype α).toOuterMeasure {a | a ∈ targets} ≤
      (targets.length : ℝ≥0∞) * ((1 : ℝ≥0∞) / Fintype.card α) := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFintype, one_div]
  gcongr
  exact_mod_cast (Finset.card_le_card fun a ha =>
    List.mem_toFinset.mpr (Finset.mem_filter.mp ha).2).trans (List.toFinset_card_le targets)

/-- Convert a `Finset.dens` real upper bound on `F` covering `E ⊆ ↑F` into an `ENNReal`
`toOuterMeasure` bound under `PMF.uniformOfFintype`, without comparing `DecidablePred` instances. -/
theorem toOuterMeasure_uniformOfFintype_le_of_dens_le {α : Type*} [Fintype α] [Nonempty α]
    (E : Set α) (F : Finset α) {B : ℝ}
    (hsub : E ⊆ (F : Set α)) (hdens : (F.dens : ℝ) ≤ B) :
    (PMF.uniformOfFintype α).toOuterMeasure E ≤ ENNReal.ofReal B := by
  have hB0 : 0 ≤ B := (by positivity : (0 : ℝ) ≤ (F.dens : ℝ)).trans hdens
  have hc_pos : 0 < Fintype.card α := Fintype.card_pos
  have hd : (F.card : ℝ) / Fintype.card α ≤ B := by
    simpa only [Finset.nnratCast_dens, Finset.dens_eq_card_div_card, NNRat.cast_div,
      NNRat.cast_natCast] using hdens
  have hcard_enn : (F.card : ℝ≥0∞) ≤ ENNReal.ofReal B * Fintype.card α := by
    simpa [ENNReal.ofReal_mul hB0] using
      ENNReal.ofReal_le_ofReal ((div_le_iff₀ (Nat.cast_pos.mpr hc_pos)).mp hd)
  calc (PMF.uniformOfFintype α).toOuterMeasure E
      ≤ (PMF.uniformOfFintype α).toOuterMeasure (F : Set α) :=
        MeasureTheory.measure_mono hsub
    _ = (F.card : ℝ≥0∞) * (Fintype.card α : ℝ≥0∞)⁻¹ := by
      rw [PMF.toOuterMeasure_apply_finset]
      simp [PMF.uniformOfFintype_apply]
    _ ≤ (ENNReal.ofReal B * Fintype.card α) * (Fintype.card α : ℝ≥0∞)⁻¹ := by gcongr
    _ = ENNReal.ofReal B := by
      rw [mul_assoc, ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr hc_pos.ne')
        (ENNReal.natCast_ne_top _), mul_one]

/-- Marginal identity for `PMF.uniformOfFintype` along the first projection of `e : γ ≃ α × β`. -/
theorem toOuterMeasure_uniformOfFintype_fst {α β γ : Type*}
    [Fintype α] [Nonempty α] [Finite β] [Nonempty β] [Fintype γ] [Nonempty γ]
    (e : γ ≃ α × β) (P : α → Prop) :
    (PMF.uniformOfFintype γ).toOuterMeasure {z | P (e z).1} =
      (PMF.uniformOfFintype α).toOuterMeasure {a | P a} := by
  let _ : Fintype β := Fintype.ofFinite β
  have hmap : (PMF.uniformOfFintype γ).map (Prod.fst ∘ e) = PMF.uniformOfFintype α := by
    rw [← PMF.map_comp, PMF.uniformOfFintype_map_equiv e, uniformOfFintype_prod_map_fst]
  rw [← hmap, PMF.toOuterMeasure_map_apply]
  rfl

/-- Conditional union bound for `PMF.uniformOfFintype` along `e : γ ≃ α × β`: if `¬ G` has
probability at most `p_top` on `α`, and for every `a` with `G a` the fiber bad event has
probability at most `p_bot` on `β`, then `Bad` has probability at most `p_top + p_bot` on `γ`. -/
theorem toOuterMeasure_uniformOfFintype_cond_le {α β γ : Type*}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] [Fintype γ] [Nonempty γ]
    (e : γ ≃ α × β) (G : α → Prop) (Bad : γ → Prop) {p_top p_bot : ℝ≥0∞}
    (htop : (PMF.uniformOfFintype α).toOuterMeasure {a | ¬ G a} ≤ p_top)
    (hbot : ∀ a : α, G a →
      (PMF.uniformOfFintype β).toOuterMeasure {b | Bad (e.symm (a, b))} ≤ p_bot) :
    (PMF.uniformOfFintype γ).toOuterMeasure {z | Bad z} ≤ p_top + p_bot := by
  rw [← PMF.uniformOfFintype_map_equiv e.symm, PMF.toOuterMeasure_map_apply,
    ← uniformOfFintype_prod]
  refine (toOuterMeasure_bind_le_add _ _ {a | ¬ G a} _ p_bot fun a _ ha => ?_).trans
    (add_le_add htop le_rfl)
  rw [PMF.toOuterMeasure_map_apply]
  exact hbot a (not_not.mp ha)

end Cslib.Probability.PMF
