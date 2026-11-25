/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

/-!
# The median of a finite family of reals

`Cslib.median v` is the lower median of a finite family `v : ι → ℝ`: the least value `v i` that is
weakly above at least half of the family (and `0` for an empty family). It is characterized by
majorities: if more than half of the family lies weakly below `b`, so does the median
(`Cslib.median_le`), and if more than half lies weakly above `a`, so does the median
(`Cslib.le_median`). Hence a majority within `t` of `μ` forces the median within `t` of `μ`
(`Cslib.abs_median_sub_le`), the step that turns estimates that are good with probability above a
half into one that is good with high probability [AlonMatiasSzegedy1999, Theorem 2.2].

`Finset.exists_median` (`CslibFrontier.Foundations.Data.Finset.Quantile`) only asserts that a median
element exists; `Cslib.median` is a chosen value, so it can appear in an algorithm's output. It is
unrelated to `Cslib.BitString.median`, the coordinatewise majority of three bit strings; under
`open Cslib.BitString` write `Cslib.median` explicitly.

## Main definitions

* `Cslib.median`: the lower median of a finite family of reals.

## Main results

* `Cslib.median_le`, `Cslib.le_median`: a strict majority below (above) a bound puts the median
  below (above) it.
* `Cslib.abs_median_sub_le`: the median of a family with a strict majority within `t` of `μ` is
  within `t` of `μ`.
* `Cslib.median_const`: the median of a nonempty constant family.

## References

* [N. Alon, Y. Matias, M. Szegedy, *The space complexity of approximating the frequency
  moments*, Theorem 2.2][AlonMatiasSzegedy1999]
-/

public section

namespace Cslib

open Finset

variable {ι : Type*} [Fintype ι]

/-- The lower median of a finite family of reals: the least value `v i` with at least half of the
family weakly below it (zero for an empty family). -/
noncomputable def median (v : ι → ℝ) : ℝ :=
  open scoped Classical in
  if h : ({i | Fintype.card ι ≤ 2 * #{j | v j ≤ v i}} : Finset ι).Nonempty then
    (univ.filter fun i => Fintype.card ι ≤ 2 * #{j | v j ≤ v i}).inf' h v
  else 0

/-- If more than half of the family lies weakly below `b`, so does the median. -/
theorem median_le {v : ι → ℝ} {b : ℝ} (hb : Fintype.card ι < 2 * #{j | v j ≤ b}) :
    median v ≤ b := by
  classical
  obtain ⟨i₀, hi₀, hmax⟩ := exists_max_image ({j | v j ≤ b} : Finset ι) v
    (card_pos.1 (by omega))
  have hcand : Fintype.card ι ≤ 2 * #{j | v j ≤ v i₀} := by
    have := card_le_card (s := {j | v j ≤ b}) (t := {j | v j ≤ v i₀})
      fun j hj => mem_filter.2 ⟨mem_univ _, hmax j hj⟩
    omega
  have hmem : i₀ ∈ univ.filter fun i => Fintype.card ι ≤ 2 * #{j | v j ≤ v i} :=
    mem_filter.2 ⟨mem_univ _, hcand⟩
  unfold median
  split_ifs with h
  · exact (inf'_le _ (by convert hmem)).trans (mem_filter.1 hi₀).2
  · exact absurd ⟨i₀, by convert hmem⟩ h

/-- If more than half of the family lies weakly above `a`, so does the median. -/
theorem le_median {v : ι → ℝ} {a : ℝ} (ha : Fintype.card ι < 2 * #{j | a ≤ v j}) :
    a ≤ median v := by
  classical
  unfold median
  split_ifs with h
  · refine le_inf' _ _ fun i hi => le_of_not_gt fun hlt => ?_
    have hi := (mem_filter.1 hi).2
    have hdisj : Disjoint ({j | v j ≤ v i} : Finset ι) ({j | a ≤ v j} : Finset ι) :=
      disjoint_filter.2 fun _ _ h1 h2 => not_lt_of_ge h2 (h1.trans_lt hlt)
    have := card_union_of_disjoint hdisj ▸ card_le_univ (({j | v j ≤ v i} : Finset ι) ∪ _)
    omega
  · obtain ⟨j₀, -⟩ : ({j | a ≤ v j} : Finset ι).Nonempty := card_pos.1 (by omega)
    obtain ⟨i₀, -, hmax⟩ := exists_max_image univ v ⟨j₀, mem_univ _⟩
    refine absurd ⟨i₀, mem_filter.2 ⟨mem_univ _, ?_⟩⟩ h
    rw [filter_true_of_mem fun j _ => hmax j (mem_univ _), card_univ]; omega

/-- **The median of a majority**: if more than half of the family lies within `t` of `μ`, so does
the median. -/
theorem abs_median_sub_le {v : ι → ℝ} {μ t : ℝ}
    (hv : Fintype.card ι < 2 * #{j | |v j - μ| ≤ t}) : |median v - μ| ≤ t := by
  classical
  have hlo := card_le_card (s := {j | |v j - μ| ≤ t}) (t := {j | μ - t ≤ v j}) fun j hj => by
    simp only [mem_filter, mem_univ, true_and, abs_le] at hj ⊢; linarith
  have hhi := card_le_card (s := {j | |v j - μ| ≤ t}) (t := {j | v j ≤ μ + t}) fun j hj => by
    simp only [mem_filter, mem_univ, true_and, abs_le] at hj ⊢; linarith
  rw [abs_le]
  exact ⟨by linarith [le_median (v := v) (a := μ - t) (by omega)],
    by linarith [median_le (v := v) (b := μ + t) (by omega)]⟩

/-- The median of a nonempty constant family is the constant. -/
@[simp] theorem median_const [Nonempty ι] (c : ℝ) : median (fun _ : ι => c) = c := by
  have := Fintype.card_pos (α := ι)
  refine le_antisymm (median_le ?_) (le_median ?_) <;>
    (simp only [le_refl, Finset.filter_true, card_univ]; omega)

end Cslib
