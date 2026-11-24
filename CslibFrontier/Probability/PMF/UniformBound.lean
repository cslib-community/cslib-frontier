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
  have hne_zero : (Fintype.card α : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hne_top : (Fintype.card α : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hcast : ((∑ a : α, f a : ℕ) : ℝ≥0∞) ≤ (C : ℝ≥0∞) * (Fintype.card α : ℝ≥0∞) := by
    exact_mod_cast hle
  calc
    (Fintype.card α : ℝ≥0∞)⁻¹ * ((∑ a : α, f a : ℕ) : ℝ≥0∞)
      ≤ (Fintype.card α : ℝ≥0∞)⁻¹ * ((C : ℝ≥0∞) * (Fintype.card α : ℝ≥0∞)) := by gcongr
    _ = (C : ℝ≥0∞) * ((Fintype.card α : ℝ≥0∞)⁻¹ * (Fintype.card α : ℝ≥0∞)) := by ring
    _ = (C : ℝ≥0∞) := by rw [ENNReal.inv_mul_cancel hne_zero hne_top, mul_one]

/-- Convert a natural-number filter-cardinality bound
`B * (Finset.univ.filter P).card ≤ A * Fintype.card α` into an `ℝ≥0∞` outer-measure bound
`(PMF.uniformOfFintype α).toOuterMeasure {a : α | P a} ≤ (A : ℝ≥0∞) / (B : ℝ≥0∞)`. -/
theorem toOuterMeasure_uniformOfFintype_le_div {α : Type*} [Fintype α] [Nonempty α]
    {P : α → Prop} [DecidablePred P] {A B : ℕ} (hB : 0 < B)
    (hle : B * (Finset.univ.filter P).card ≤ A * Fintype.card α) :
    (PMF.uniformOfFintype α).toOuterMeasure {a : α | P a} ≤ (A : ℝ≥0∞) / (B : ℝ≥0∞) := by
  have h1 := PMF.toOuterMeasure_uniformOfFintype (α := α) {a : α | P a}
  simp only [Set.mem_ofPred_eq] at h1
  rw [h1]
  have hcast :
      (B : ℝ≥0∞) * ((Finset.univ.filter P).card : ℝ≥0∞) ≤
        (A : ℝ≥0∞) * (Fintype.card α : ℝ≥0∞) := by
    exact_mod_cast hle
  have hcard_ne_zero : (Fintype.card α : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcard_ne_top : (Fintype.card α : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hB_ne_zero : (B : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hB_ne_top : (B : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [ENNReal.le_div_iff_mul_le (Or.inl hB_ne_zero) (Or.inl hB_ne_top)]
  calc
    ((Finset.univ.filter P).card : ℝ≥0∞) * (Fintype.card α : ℝ≥0∞)⁻¹ * (B : ℝ≥0∞)
      = ((B : ℝ≥0∞) * ((Finset.univ.filter P).card : ℝ≥0∞)) * (Fintype.card α : ℝ≥0∞)⁻¹ := by ring
    _ ≤ ((A : ℝ≥0∞) * (Fintype.card α : ℝ≥0∞)) * (Fintype.card α : ℝ≥0∞)⁻¹ := by gcongr
    _ = (A : ℝ≥0∞) * ((Fintype.card α : ℝ≥0∞) * (Fintype.card α : ℝ≥0∞)⁻¹) := by ring
    _ = (A : ℝ≥0∞) := by rw [ENNReal.mul_inv_cancel hcard_ne_zero hcard_ne_top, mul_one]

/-- **Target-hitting union bound for `PMF.uniformOfFintype`**: a uniformly sampled `a : α` lands in
`targets` with probability at most `targets.length * (1 / Fintype.card α)`. -/
theorem toOuterMeasure_uniformOfFintype_mem_list_le {α : Type*} [Fintype α] [Nonempty α]
    (targets : List α) :
    (PMF.uniformOfFintype α).toOuterMeasure {a | a ∈ targets} ≤
      (targets.length : ℝ≥0∞) * ((1 : ℝ≥0∞) / Fintype.card α) := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFintype, one_div]
  gcongr
  have hsub : Finset.univ.filter (· ∈ {a : α | a ∈ targets}) ⊆ targets.toFinset := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    exact List.mem_toFinset.mpr ha
  exact_mod_cast (Finset.card_le_card hsub).trans (List.toFinset_card_le targets)

/-- Convert a `Finset.dens` real upper bound on `F` covering `E ⊆ ↑F` into an `ENNReal`
`toOuterMeasure` bound under `PMF.uniformOfFintype`, without comparing `DecidablePred` instances. -/
theorem toOuterMeasure_uniformOfFintype_le_of_dens_le {α : Type*} [Fintype α] [Nonempty α]
    (E : Set α) (F : Finset α) {B : ℝ}
    (hsub : E ⊆ (F : Set α)) (hdens : (F.dens : ℝ) ≤ B) :
    (PMF.uniformOfFintype α).toOuterMeasure E ≤ ENNReal.ofReal B := by
  have hB0 : 0 ≤ B := (by positivity : (0 : ℝ) ≤ (F.dens : ℝ)).trans hdens
  have hc_pos : 0 < Fintype.card α := Fintype.card_pos
  have hc_ne : (Fintype.card α : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hc_pos.ne'
  have hc_top : (Fintype.card α : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hcard_real : (F.card : ℝ) ≤ B * (Fintype.card α : ℝ) := by
    have hd : (F.card : ℝ) / (Fintype.card α : ℝ) ≤ B := by
      simpa only [Finset.nnratCast_dens, Finset.dens_eq_card_div_card, NNRat.cast_div,
        NNRat.cast_natCast] using hdens
    exact (div_le_iff₀ (Nat.cast_pos.mpr hc_pos)).mp hd
  have hcard_enn : (F.card : ℝ≥0∞) ≤ ENNReal.ofReal B * (Fintype.card α : ℝ≥0∞) := by
    have h1 := ENNReal.ofReal_le_ofReal hcard_real
    rwa [ENNReal.ofReal_natCast, ENNReal.ofReal_mul hB0, ENNReal.ofReal_natCast] at h1
  calc (PMF.uniformOfFintype α).toOuterMeasure E
      ≤ (PMF.uniformOfFintype α).toOuterMeasure (F : Set α) :=
        MeasureTheory.measure_mono hsub
    _ = (F.card : ℝ≥0∞) * (Fintype.card α : ℝ≥0∞)⁻¹ := by
        rw [PMF.toOuterMeasure_apply_finset]
        simp only [PMF.uniformOfFintype_apply, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (ENNReal.ofReal B * (Fintype.card α : ℝ≥0∞)) * (Fintype.card α : ℝ≥0∞)⁻¹ := by
        gcongr
    _ = ENNReal.ofReal B := by
        rw [mul_assoc, ENNReal.mul_inv_cancel hc_ne hc_top, mul_one]

/-- Marginal identity for `PMF.uniformOfFintype` along the first projection of `e : γ ≃ α × β`. -/
theorem toOuterMeasure_uniformOfFintype_fst {α β γ : Type*}
    [Fintype α] [Nonempty α] [Finite β] [Nonempty β] [Fintype γ] [Nonempty γ]
    (e : γ ≃ α × β) (P : α → Prop) :
    (PMF.uniformOfFintype γ).toOuterMeasure {z | P (e z).1} =
      (PMF.uniformOfFintype α).toOuterMeasure {a | P a} := by
  let _ : Fintype β := Fintype.ofFinite β
  have hfn : (fun z : γ => (e z).1) = Prod.fst ∘ e := rfl
  have hmap : (PMF.uniformOfFintype γ).map (fun z => (e z).1) = PMF.uniformOfFintype α := by
    rw [hfn, ← PMF.map_comp, PMF.uniformOfFintype_map_equiv e, uniformOfFintype_prod_map_fst]
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
  refine (toOuterMeasure_bind_le_add _ _ {a | ¬ G a} _ p_bot ?_).trans (add_le_add htop le_rfl)
  intro a _ ha
  rw [PMF.toOuterMeasure_map_apply]
  exact hbot a (not_not.mp ha)

end Cslib.Probability.PMF
