/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
import CslibFrontier.Probability.PMF.UniformBridge
import CslibFrontier.Probability.Quantile
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

/-!
# Finite quantiles with ties

For any proportion between zero and one, a nonempty finite collection of ordered scores has a
pivot whose weak lower and upper level sets contain the corresponding proportions. Equal scores
belong to both level sets; no injectivity or tie-breaking assumption is required.

## Main results

* `Finset.exists_quantile`: select a pivot retaining the requested proportions on both sides.
* `Finset.exists_median`: select a median pivot with at least half of the elements on each side.
* `Fintype.exists_forall_card_filter_le_card_filter`: some value of a function on a finite type is
  taken at least as often as any other.

## References

* [*Threshold Circuits as Decision Trees and Finite-State Programs*, Lemma 2.1]
  [ThresholdCircuitRepresentations2026]
-/

public section

namespace Finset

variable {α β : Type*} [LinearOrder β]

/-- A finite score collection has a quantile with large weak level sets on both sides.
The pivot itself is retained on both sides, so the statement includes tied scores. -/
theorem exists_quantile (s : Finset α) (hs : s.Nonempty) (score : α → β)
    {a : ℝ} (ha : 0 ≤ a) (ha₁ : a ≤ 1) :
    ∃ p ∈ s, a * s.card ≤ ((s.filter fun x => score x ≤ score p).card : ℝ) ∧
      (1 - a) * s.card ≤ ((s.filter fun x => score p ≤ score x).card : ℝ) := by
  classical
  have : Nonempty s := hs.to_subtype
  obtain ⟨_, ⟨p, rfl⟩, hlt, hle⟩ :=
    Cslib.Probability.PMF.exists_quantile (Cslib.Probability.PMF.uniformOfFintype s)
      (fun x : s => score x.val) ha ha₁
  rw [Cslib.Probability.PMF.sum_subtype_uniformOfFintype_ite_toReal s (score · < score p.val)]
    at hlt
  rw [Cslib.Probability.PMF.sum_subtype_uniformOfFintype_ite_toReal s (score · ≤ score p.val)]
    at hle
  have hpos : (0 : ℝ) < s.card := Nat.cast_pos.mpr hs.card_pos
  have hcompl : ((s.filter fun x => score x < score p.val).card : ℝ) +
      ((s.filter fun x => score p.val ≤ score x).card : ℝ) = s.card := by
    simpa only [not_lt] using
      (Nat.cast_add _ _).symm.trans
        (congrArg Nat.cast (s.card_filter_add_card_filter_not fun x => score x < score p.val))
  refine ⟨p.val, p.property, (le_div_iff₀ hpos).mp hle, ?_⟩
  have := (div_le_iff₀ hpos).mp hlt
  linarith

/-- Every nonempty finite set `s` equipped with a linearly ordered score `score : α → β` has a
median element `p ∈ s` with at least half of `s` weakly below `score p` and at least half weakly
above `score p`. -/
theorem exists_median (s : Finset α) (hs : s.Nonempty) (score : α → β) :
    ∃ p ∈ s, s.card ≤ 2 * (s.filter fun x => score x ≤ score p).card ∧
      s.card ≤ 2 * (s.filter fun x => score p ≤ score x).card := by
  obtain ⟨p, hp, hlo, hhi⟩ := s.exists_quantile hs score (a := 1 / 2) (by norm_num) (by norm_num)
  refine ⟨p, hp, ?_, ?_⟩
  · exact_mod_cast
      (by linarith : (s.card : ℝ) ≤ 2 * ((s.filter fun x => score x ≤ score p).card : ℝ))
  · exact_mod_cast
      (by linarith : (s.card : ℝ) ≤ 2 * ((s.filter fun x => score p ≤ score x).card : ℝ))

/-- **Plurality**: some value of a function on a finite type is taken at least as often as any
other. -/
theorem _root_.Fintype.exists_forall_card_filter_le_card_filter {ι α : Type*} [Fintype ι]
    [Nonempty α] [DecidableEq α] (f : ι → α) : ∃ a, ∀ b, #{i | f i = b} ≤ #{i | f i = a} := by
  rcases isEmpty_or_nonempty ι with h | ⟨⟨i₀⟩⟩
  · exact ⟨Classical.arbitrary α, fun b ↦ by simp [univ_eq_empty]⟩
  obtain ⟨i, -, hi⟩ := univ.exists_max_image (fun i ↦ #{j | f j = f i}) ⟨i₀, mem_univ _⟩
  refine ⟨f i, fun b ↦ ?_⟩
  by_cases hb : ∃ j, f j = b
  · obtain ⟨j, rfl⟩ := hb
    exact hi j (mem_univ _)
  · simp only [not_exists] at hb
    rw [filter_false_of_mem fun j _ ↦ hb j, Finset.card_empty]
    exact Nat.zero_le _

end Finset
