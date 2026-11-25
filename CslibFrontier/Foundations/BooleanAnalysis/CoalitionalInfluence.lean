/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Resilience
import CslibFrontier.Foundations.BooleanAnalysis.Decomposition
import Mathlib.Tactic.Linarith

/-!
# Coalitional influence

The coalitional influence of a set `J` of voters on a Boolean function `f` is the probability,
over the votes outside `J`, that the voters in `J` can still change the outcome
(`BitString.coalitionInfluence` under the uniform distribution, from
`CslibFrontier.Probability.Resilience`).
Its influence **toward** an outcome `b` is the probability that `J` can make the outcome `b`, less
`Pr[f = b]` (`BitString.coalitionInfluenceToward`) [O'Donnell, Exercise 9.25][ODonnell2014].

The directed influence lies in `[0, 1]` (`BitString.coalitionInfluenceToward_nonneg`,
`BitString.coalitionInfluenceToward_le_one`) and grows with the coalition
(`BitString.coalitionInfluenceToward_mono`). For one voter it is half the influence
(`BitString.coalitionInfluenceToward_singleton`), the undirected influence is the sum of the two
directed ones (`BitString.coalitionInfluence_eq_add`), for monotone `f` a coalition does best by
voting unanimously (`BitString.coalitionInfluenceToward_eq_of_monotone`), and every nonempty
coalition controls the parity of all the voters (`BitString.coalitionInfluence_parityOn_univ`).
Parts (f) and (g) of Exercise 9.25, on Majority and Tribes, are not formalized.

## Main definitions

* `Cslib.BitString.coalitionInfluenceToward`: the coalitional influence toward an outcome.

## Main results

* `Cslib.BitString.coalitionInfluenceToward_singleton`: Exercise 9.25(a).
* `Cslib.BitString.coalitionInfluenceToward_nonneg`,
  `Cslib.BitString.coalitionInfluenceToward_le_one`: Exercise 9.25(b).
* `Cslib.BitString.coalitionInfluence_eq_add`: Exercise 9.25(c).
* `Cslib.BitString.coalitionInfluenceToward_eq_of_monotone`: Exercise 9.25(d).
* `Cslib.BitString.coalitionInfluence_parityOn_univ`: Exercise 9.25(e).

## Usage

Open `Cslib.BitString`. The book's `b ∈ {-1, 1}` is a `Bool` read through `signVal`
(`signVal true = -1`), so `Inf~^{+1}` is `coalitionInfluenceToward false` and `Inf~^{-1}` is
`coalitionInfluenceToward true`. The book's undirected `Inf~_J[f]` is
`coalitionInfluence (Probability.PMF.uniformOfFintype (ι → Bool)) J f` from
`CslibFrontier.Probability.Resilience`, which also has its single-voter case
`Cslib.BitString.coalitionInfluence_singleton` and its bounds
`Cslib.BitString.coalitionInfluence_nonneg` and `Cslib.BitString.coalitionInfluence_le_one`. For
a monotone `f`, rewrite with `Cslib.BitString.coalitionInfluenceToward_eq_of_monotone` to turn
the existential over the coalition's votes into the unanimous vote `J.piecewise (fun _ => b) z`;
small concrete cases then close by `decide` on the counts. The bribery bounds of Exercise 9.27
that use these influences are in `CslibFrontier.Foundations.BooleanAnalysis.Bribery`.

The checked client
[CslibFrontierTests/BooleanAnalysisCoalitionalInfluence.lean](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/BooleanAnalysisCoalitionalInfluence.lean)
computes the directed influences of one and two voters on the conjunction `threshold 2 2` (by
parts (a) and (d), and their sum by part (c)) and of one voter on the parity of two voters (by
unfolding the definition and by parts (b), (c) and (e)).

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- The **coalitional influence toward `b`** of a set `J` of voters on `f`
[O'Donnell, Exercise 9.25][ODonnell2014]: the probability, over the votes `z` outside `J`, that the
voters in `J` can make the outcome `b`, minus the probability that the outcome is `b`. -/
@[expose] noncomputable def coalitionInfluenceToward (b : Bool) (J : Finset ι)
    (f : (ι → Bool) → Bool) : ℝ :=
  (𝔼 z, if ∃ y, f (J.piecewise y z) = b then 1 else 0) - 𝔼 x, if f x = b then 1 else 0

/-- **The directed coalitional influence is nonnegative** [O'Donnell, Exercise 9.25(b)]
[ODonnell2014]: if `f(z) = b` then `J` can make the outcome `b` by voting as in `z`. -/
theorem coalitionInfluenceToward_nonneg (b : Bool) (J : Finset ι) (f : (ι → Bool) → Bool) :
    0 ≤ coalitionInfluenceToward b J f := by
  rw [coalitionInfluenceToward, sub_nonneg]
  refine expect_le_expect fun z _ => ?_
  by_cases h : f z = b
  · simp [h, show ∃ y, f (J.piecewise y z) = b from ⟨z, by rwa [piecewise_same]⟩]
  · simp only [h, ↓reduceIte]
    split_ifs <;> norm_num

/-- **The directed coalitional influence is at most one** [O'Donnell, Exercise 9.25(b)]
[ODonnell2014]. -/
theorem coalitionInfluenceToward_le_one (b : Bool) (J : Finset ι) (f : (ι → Bool) → Bool) :
    coalitionInfluenceToward b J f ≤ 1 := by
  have h1 : (𝔼 z, if ∃ y, f (J.piecewise y z) = b then (1 : ℝ) else 0) ≤ 1 :=
    expect_le univ_nonempty fun z _ => by split_ifs <;> norm_num
  have h0 : (0 : ℝ) ≤ 𝔼 x, if f x = b then 1 else 0 :=
    expect_nonneg fun x _ => by split_ifs <;> norm_num
  rw [coalitionInfluenceToward]
  linarith

/-- A larger coalition has at least the directed influence of a smaller one. -/
theorem coalitionInfluenceToward_mono (b : Bool) {J K : Finset ι} (hJK : J ⊆ K)
    (f : (ι → Bool) → Bool) : coalitionInfluenceToward b J f ≤ coalitionInfluenceToward b K f := by
  rw [coalitionInfluenceToward, coalitionInfluenceToward, sub_le_sub_iff_right]
  refine expect_le_expect fun z _ => ?_
  split_ifs with h h' <;> norm_num
  obtain ⟨y, hy⟩ := h
  refine absurd ⟨J.piecewise y z, ?_⟩ h'
  convert hy using 2
  funext j
  by_cases hj : j ∈ J
  · simp [piecewise, hj, hJK hj]
  · by_cases hk : j ∈ K <;> simp [piecewise, hj, hk]

/-- **The directed coalitional influence of one voter is half its influence**
[O'Donnell, Exercise 9.25(a)][ODonnell2014]: `Inf~_{i}^b[f] = Infᵢ[f] / 2`; the undirected
`coalitionInfluence_singleton` is the influence itself. -/
theorem coalitionInfluenceToward_singleton (b : Bool) (i : ι) (f : (ι → Bool) → Bool) :
    coalitionInfluenceToward b {i} f = influence i (fun x => signVal (f x)) / 2 := by
  set φ : (ι → Bool) → ℝ := fun x => if f x = b then 1 else 0
  have hmean := expect_update_false_add_update_true φ i
  have hex (z : ι → Bool) : (∃ y : ι → Bool, f (Function.update z i (y i)) = b) ↔
      f (Function.update z i false) = b ∨ f (Function.update z i true) = b := by
    refine ⟨fun ⟨y, hy⟩ => ?_, ?_⟩
    · cases h : y i <;> rw [h] at hy
      exacts [Or.inl hy, Or.inr hy]
    · rintro (h | h)
      exacts [⟨fun _ => false, h⟩, ⟨fun _ => true, h⟩]
  have hz (z : ι → Bool) : (if ∃ y : ι → Bool, f (Function.update z i (y i)) = b then (1 : ℝ)
      else 0) = (φ (Function.update z i false) + φ (Function.update z i true)) / 2 +
        derivative i (fun x => signVal (f x)) z ^ 2 / 2 := by
    simp only [hex, φ, derivative]
    cases b <;> cases f (Function.update z i false) <;> cases f (Function.update z i true) <;>
      norm_num
  rw [expect_add_distrib] at hmean
  simp only [coalitionInfluenceToward, piecewise_singleton, hz, expect_add_distrib,
    ← expect_div, influence]
  simp only [φ] at hmean ⊢
  linarith

/-- **Coalitional influence splits by direction** [O'Donnell, Exercise 9.25(c)][ODonnell2014]:
`Inf~_J[f] = Inf~_J^{true}[f] + Inf~_J^{false}[f]`. For each `z` the coalition can make the outcome
`true` or `false` or both, and both exactly when it can change the outcome. -/
theorem coalitionInfluence_eq_add (J : Finset ι) (f : (ι → Bool) → Bool) :
    coalitionInfluence (Probability.PMF.uniformOfFintype (ι → Bool)) J f =
      coalitionInfluenceToward true J f + coalitionInfluenceToward false J f := by
  have hz (z : ι → Bool) : (if IsUndetermined J f z then (1 : ℝ) else 0) +
      ((if f z = true then 1 else 0) + (if f z = false then 1 else 0)) =
      (if ∃ y, f (J.piecewise y z) = true then (1 : ℝ) else 0) +
        (if ∃ y, f (J.piecewise y z) = false then 1 else 0) := by
    have hne : IsUndetermined J f z ↔
        (∃ y, f (J.piecewise y z) = true) ∧ ∃ y, f (J.piecewise y z) = false := by
      rw [isUndetermined_iff_outside]
      simp only [PartialAssignment.fill_outside]
      constructor
      · rintro ⟨y, y', h⟩
        cases hy : f (J.piecewise y z) <;> rw [hy] at h
        · exact ⟨⟨y', by simpa using h.symm⟩, ⟨y, hy⟩⟩
        · exact ⟨⟨y, hy⟩, ⟨y', by simpa using h.symm⟩⟩
      · rintro ⟨⟨y, hy⟩, ⟨y', hy'⟩⟩
        exact ⟨y, y', by rw [hy, hy']; decide⟩
    have hself : f (J.piecewise z z) = f z := by rw [piecewise_same]
    rw [if_congr hne rfl rfl]
    cases hfz : f z
    · have hf : ∃ y, f (J.piecewise y z) = false := ⟨z, hself.trans hfz⟩
      by_cases ht : ∃ y, f (J.piecewise y z) = true <;> simp [ht, hf]
    · have ht : ∃ y, f (J.piecewise y z) = true := ⟨z, hself.trans hfz⟩
      by_cases hf : ∃ y, f (J.piecewise y z) = false <;> simp [ht, hf]
  have hsum := congrArg (fun φ => 𝔼 z, φ z) (funext hz)
  simp only [expect_add_distrib] at hsum
  have hone :
      (𝔼 x, ((if f x = true then (1 : ℝ) else 0) + (if f x = false then 1 else 0))) = 1 := by
    refine (expect_congr rfl fun x _ => ?_).trans (Fintype.expect_const 1)
    cases f x <;> norm_num
  rw [expect_add_distrib] at hone
  rw [coalitionInfluence_uniformOfFintype, coalitionInfluenceToward, coalitionInfluenceToward]
  linarith

/-- **Coalitional influence on monotone functions** [O'Donnell, Exercise 9.25(d)][ODonnell2014]:
for monotone `f` the best way for `J` to make the outcome `b` is to vote `b` unanimously, so
`Inf~_J^b[f] = Pr[f(b_J, z) = b] - Pr[f = b]`. -/
theorem coalitionInfluenceToward_eq_of_monotone {f : (ι → Bool) → Bool} (hf : Monotone f)
    (b : Bool) (J : Finset ι) :
    coalitionInfluenceToward b J f =
      (𝔼 z, if f (J.piecewise (fun _ => b) z) = b then 1 else 0) -
        𝔼 x, if f x = b then 1 else 0 := by
  have hz (z : ι → Bool) :
      (∃ y, f (J.piecewise y z) = b) ↔ f (J.piecewise (fun _ => b) z) = b := by
    refine ⟨fun ⟨y, hy⟩ => ?_, fun h => ⟨_, h⟩⟩
    cases b
    · have h := hf (J.piecewise_le_piecewise (fun j => Bool.false_le (y j)) (le_refl z))
      rw [hy] at h
      exact le_bot_iff.1 h
    · have h := hf (J.piecewise_le_piecewise (fun j => Bool.le_true (y j)) (le_refl z))
      rw [hy] at h
      exact top_le_iff.1 h
  simp only [coalitionInfluenceToward, hz]

/-- **Every coalition controls a parity** [O'Donnell, Exercise 9.25(e)][ODonnell2014]: any
nonempty `J` has coalitional influence `1` on the parity of all the voters. -/
theorem coalitionInfluence_parityOn_univ {J : Finset ι} (hJ : J.Nonempty) :
    coalitionInfluence (Probability.PMF.uniformOfFintype (ι → Bool)) J (parityOn univ) = 1 := by
  obtain ⟨j, hj⟩ := hJ
  refine coalitionInfluence_eq_one_of_forall _ fun z =>
    ((isUndetermined_singleton_iff j).2 ?_).mono (singleton_subset_iff.2 hj)
  rw [parityOn_update_not (mem_univ j)]
  cases parityOn univ z <;> decide

end Cslib.BitString
